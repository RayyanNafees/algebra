
class Algebra: pass


import factors
from functools import wraps

def equation(func):
    '''Decorator for manipulating equations.
       (rest of the functions are generalised only for polynomials.)'''
    @wraps(func)
    def wrapper(self, term: str):      #change the signature as needed (Ex: term = None)
        term = Algebra(term)

        if iseqn(self) and not iseqn(term):     # equation with single term
            return equate(func(self.lhs,term), func(self.rhs,term))

        elif iseqn(self) and iseqn(term):       # equation with another equation
            return equate(func(self.lhs,term.lhs), func(self.rhs,term.rhs))

        return func(self, term)   # for funcs signatured 1 arg: func(self, term) if term else func(self)
    return wrapper


iseqn  = lambda  src: any(i in str(src) for i in ('=','<','>','<=','>='))
equify = lambda expr: str(expr).replace('**','^').replace(' ','').replace('==','=')

equate = lambda l, r, sign ='=': Algebra(f'{l}{sign}{r}')
simpler = lambda num: i if (i:=int(num)) == (f:=float(num)) else f


def var(term: str) -> str:
    '''Returns the variable of the supplied term.'''
    def var(term: str) -> str:
        '''The main func responsible...'''
        term = equify(term)
        var = []
        for n,i in enumerate(term):
            if i.isalpha():
                var.append(i)
            if i == '^':
                var.extend(['^'+term[n+1]])

        return ''.join(var)

    if '/' not in str(term): return var(term)

    num, den = term.split('/')
    if bool(var(den)) and bool(var(num)):           # if both num & den have variables
        return f'{var(num)}/{var(den)}'

    elif bool(var(den)) and not bool(var(num)):     # if num does not have variables but den has
        return f'1/{var(den)}'

    elif not bool(var(den)) and bool(var(num)):     # If den does not have variables but num has
        return var(term)
    else: return ''                                 # If none of'em has variables


def const(term: str) -> int:
    '''Returns the constant integer of the supplied term.'''
    if '/'  in (term:= str(term)):
        n,d = term.split('/')
        n,d = n.replace(var(n),''), d.replace(var(d),'')
        return simpler(const(n)/const(d))

    num = str(term).replace(var(term),'')

    if '.' in num: return float(num)
    if num == '-': return -1
    elif num =='': return 1

    return int(num)


def alpha(term: str) -> str:
    '''docstring'''
    return ''.join(a for a in str(term) if a.isalpha())


def like(term1, term2: str) -> bool:
    '''docstring'''
    return var(term1) == var(term2)


def terms(expr: str) -> list:
    '''Returns a list of terms in the supplied expression'''
    eqn = equify(expr).replace('+','|').replace('-','|-').replace('=','|=|')
    terms = eqn.split('|')

    for n,i in enumerate(terms.copy()):
        if i == '': terms.remove(i)
        try:
            terms[n] = simpler(eval(i))
        except: continue

    return terms


def unterm(termz: list) -> Algebra:
    '''Returns the algebraic expression from the supplied list of terms.'''
    expr = [ str(i) for i in termz ]

    for n,i in enumerate(expr):
        if var(i) != '':
            if const(i) == 1:
                expr[n] = var(i)
            elif const(i) == (-1):
                expr[n] = '-'+var(i)

        if const(i) == 0:
            expr.remove(i)

    return Algebra('+'.join(expr).replace('+-','-').replace('+=+','='))



def constz(expr: str) -> tuple:
    '''docstring'''
    return tuple(map(const, terms(expr)))


def varz(expr: str) -> tuple:
    '''docstring'''
    return tuple(map(var, terms(expr)))


def alphaz(expr: str) -> tuple:
    '''docstring'''
    return tuple(sorted(set(map(alpha,terms(expr)))))



def pow_dict(expr: str) -> dict:
    '''docstring'''
    return {i : [term for term in terms(expr) if power(term) == i] for i in range(deg(expr),-1,-1)}


def var_dict(expr: str) -> dict:
    '''docstring'''
    return {i : [v for v in terms(expr) if var(v) == i] for i in varz(expr)}


def alpha_dict(expr: str) -> dict:
    '''docstring'''
    return {i : [trm for trm in terms(expr) if alpha(trm) == i] for i in alphaz(expr)}


termd, liked, alphad = pow_dict, var_dict, alpha_dict


def power(term: str) -> int:
    '''docstring'''
    _var = var(term)

    if '^' in _var:
        return int(_var.replace(alpha(term),'').replace('^', ''))
    elif _var == '':
        return 0
    else:
        return 1


def deg(expr: str) -> int:
    '''docstring'''
    return max( power(i) for i in terms(expr))

def simplified(expr: str) -> str:
    '''docstring'''
    return unterm(str(num) + var for var,num in \
                 {var : sum(const(i) for i in val) for var,val in liked(expr).items()}.items())

def pow_sorted(expr: str) -> str:
    '''docstring'''
    return unterm(factors.sum(termd(expr).values()))


def sort(expr: str) -> str:
    '''Returns a sorted format of the supplied expression.'''
    alp = 'abcdefghijklmnopqrstuvwxyz'
    sorted_alg = []
    ind = lambda i: alp.index(alpha(i))
    expr = str(expr).lower()

    for v in termd(pow_sorted(expr)).values():
        indlist = [ind(i) for i in v]
        while bool(indlist):
            for i in v:
                if ind(i) == min(indlist):
                    sorted_alg.append(i)
                    v.remove(i)
                    indlist.remove(ind(i))

    return unterm(sorted_alg)


def common(expr: str) -> str:
    '''Returns the common term from the (two) supplied polynomial.
       len(expr) == 2'''
    assert len(terms(expr)) == 2, 'Only binomials supported !'

    from factors import prime_factorise as pf

    comm = lambda l,n: [trm for trm in min(terms(l),terms(n)) if trm in max(terms(l),terms(n))]
    coms = [pf(const(i)) + tuple(alpha(i) for num in range(power(i))) for i in terms(expr)]

    for n,i in enumerate(coms.copy()):
        coms[n+1] = com(i,coms[n+1])

    return coms[-1]


def quad_eq(a: int, b: int, c: int) -> list:
    '''Returns the roots of the supplied terms of a quadratic equation.
       Equation must be of the form: "ax^2 + bx + c" (for variable x)'''
    a, b, c = int(a),int(b),int(c)

    D = (b**2) - (4*a*c)

    if D > 0:
        num1, num2 = (-b + D**0.5)/(2*a) , (-b - D**0.5)/(2*a)
        return [const(num1), const(num2)]
    elif D == 0:
        return [const((-b)/(2*a))]
    elif D < 0:
        return []



#_________________________<class '__name__.Algebra'>_________________________________________________

class Algebra:
    '''Purpose'''

    def __init__(self,term: str) -> None:
        '''Initializes the equation for the Algebra object.'''
        self.eq = equify(term)

        if iseqn(term):
            eq = self.eq.split('=')
            self.lhs = Algebra(eq[0])
            self.rhs = Algebra(eq[-1])


    def copy(self): return unterm(trm for trm in self)

    def __iter__(self): return iter(terms(self))


# booleans:

    def __contains__(self, item) -> bool:
        '''Returns item in self'''
        elems = [i for i in self]
        nums = [const(i) for i in self]
        alps = [var(i) for i in self]
        return item in (elems + nums + alps + [str(n) for n in nums])


    def __lt__(self, expr: str) -> bool:
        '''Returns self < expr ( for variables == 1).'''
        expr = Algebra(expr)
        one = {a : 1 for a in alphaz(self)}
        self_int = self.solve_for(**one)
        expr_int = expr.solve_for(**one)
        return self_int < expr_int


    def __eq__(self, expr: str) -> bool:
        '''docstring'''
        return set(terms(simplified(self))) == set(terms(simplified(expr)))

    def __ne__(self, expr: str) -> bool:
        '''docstring'''
        return not self == expr

    def __gt__(self, expr: str) -> bool:
        '''docstring'''
        return False if self == expr else not self < expr

    def __le__(self, expr: str) -> bool:
        '''docstring'''
        return self < expr or self == expr

    def __ge__(self, expr: str) -> bool:
        '''docstring'''
        return self > expr or self == expr


# calculators:

    @equation
    def __add__(self, term: str) -> str:
        '''docstring'''
        return simplified(f'{self}+{term}'.replace('+-','-')) if term != -Algebra(self) else 0


    def __sub__ (self, term: str) -> str:
        '''docstring'''
        return self + (-(Algebra(term))) if term != self else 0

    def __radd__(self, value: str) -> str:
        '''docstring'''
        return self + value

    def __rsub__(self, value: str) -> str:
        '''docstring'''
        return -(self) + value

    def __rmul__(self, term: str) -> str:
        '''docstring'''
        return self * term


    @equation
    def __mul__(self, term: str) -> str:
        '''Returns self * term'''
        def mul(Self, val: str) -> str:
            num_mul = const(Self) * const(val)

            if bool(var(val)) == False:
                var_mul = var(Self)

            elif alpha(Self) != alpha(val):
                var_mul = var(Self) + var(val)

            elif alpha(Self) == alpha(val):
                var_mul = alpha(Self) + '^' + str(power(Self) + power(val))

            return str(num_mul) + var_mul

        prod = []
        for s in self:
            for v in terms(term):
                prod.append(mul(s,v))

        return simplified(unterm(prod))


    @equation
    def __pow__(self, expt: int) -> str:
        '''Returns self**expt'''
        assert (e:=int(expt)) > 0 ,'expt should be a whole no.'

        prod = 1
        for i in range(int(e)): prod *= self

        prod.sort()
        return prod


    def __truediv__(self, term: str) -> str:
        '''Returns self / term'''
        if len(terms(term)) == 1:
            if const(term) == 1:   return self
            elif const(term) == 0: raise ZeroDivisionError('devision by zero')

        elif self == term: return 1

        def div(Self, val, /):
            num_div = const(Self)/const(val)
            if like(Self,val):
                var_div = ''
            elif alpha(Self) == alpha(val):
                exp = power(Self) - power(val)
                suffix = '^' + str(exp) if exp != 1 else ''
                var_div = alpha(Self) + suffix
            else:
                var_div = var(Self)+'/'+var(val)

            if num_div == int(num_div):
                num_div = int(num_div)

            return str(num_div) + var_div

        first = lambda eqn: terms(pow_sorted(eqn))[0]

        quot = []
        rem = self.copy()
        val = Algebra(term)
        trm = first(term)
        while True:
            quo = div(first(rem),trm)
            quot.append(quo)
            rem -= val*quo
            rem.simplify() if type(rem) != int else None
            rem.pow_sort() if type(rem) != int else None
            if deg(rem) < deg(val):
                self.rem = rem
                break

        return unterm(quot)


    def __floordiv__(self, term: str) -> str:
        '''docstring'''
        return self/term

    def __mod__(self, term: str) -> str:
        '''docstring'''
        if (rem := self - (self/term * term))!= 0:
            return rem
        else: return 0


# uninumericals:

    def __invert__(self): return -(self +1)

    def __pos__(self): return self

    def __neg__(self): return unterm(str(-(const(i))) + var(i) for i in self)

    def __abs__(self): return unterm(str(abs(const(i))) + var(i) for i in self)

    def __len__(self): return len(terms(self))

    def __int__(self): return int(sum(constz(self)))


# etcetra:

    def simplify(self) -> None:
        '''Simplifies the self.'''
        self.eq = simplified(self)


    def sort(self) -> None:
        '''Sorts the different terms in self.'''
        alp = 'abcdefghijklmnopqrstuvwxyz'[::-1]
        sorted_alg = []
        ind = lambda i: alp.index(alpha(i))

        for v in termd(pow_sorted(self)).values():
            indlist = [ind(i) for i in v]
            while bool(indlist):
                for i in v:
                    if ind(i) == max(indlist):
                        sorted_alg.append(i)
                        v.remove(i)
                        indlist.remove(ind(i))

        self.eq = unterm(sorted_alg)


    def pow_sort(self) -> None:
        '''Sorts different terms of self on the basis of their exponents.'''
        self.eq = pow_sorted(self)


    def draw_graph(self, extent: range = None) -> 'graph':
        from matplotlib.pyplot import title, xlabel, ylabel, plot, show

        extent = extent if extent else \
                 range(int(2*min(self.roots())),int(2*max(self.roots())))

        if deg(self) == 2:
            x = [i for i in extent]
            y = [self.solve_for(**{f'{alphaz(self)[1]}':i}) for i in x]

        title(str(self.eq))
        xlabel('x-axis ->')
        ylabel('y-axis ->')

        x_axis = plot(list(extent),[0 for i in extent],color='black',linewidth = 1)
        y_axis = plot([0 for i in range(-100,100)],[i for i in range(-100,100)],color='black',linewidth = 1)

        plot(x,y,linewidth=1)
        show()


    def graph(self) -> None:
        '''Plots the supplied equation on Cartesian Plane.'''
        # First To install matplotlib via pip
        # Then, to know the correct syntax.
        import matplotlib.pyplot as plt
        plt.plot([1, 2, 3, 4], [1, 4, 9, 16],linewidth = 1)       #Add([x roots],[y roots])
        plt.title(str(self.eq))
        plt.text(absc,ordi,str(self.roots())) # add abscissa & ordinate to position the text
        plt.xlabel('x-axis ->')
        plt.ylabel('y-axis ->')
        plt.show()


        # This is actually NOT as simple as it looks !


    def solve_for(self, **constants: int) -> int:
        '''Returns the solution of the equaton for the supplied dict of var & constant value.'''
        nums = []
        for i in self:
            if alpha(i) == '':
                nums.append(i)
            else:
                exp = power(i)
                nums.append(const(i)*(constants[alpha(i)]**exp))

        return sum(nums)


    def roots(self) -> list:
        '''Returns a list of roots'''
        assert len(alphaz(self)) == 2, 'Supports one variable for one eqn.'

        eqn = pow_sorted(simplified(self))

        if deg(eqn) ==2:
            return quad_eq(constz(eqn)[0],
                           constz(eqn)[1],
                           constz(eqn)[2])

        if type(cons := terms(eqn)[-1]) == int:
            pos_facts = [p for p in range(1,cons+1) if not cons%p]
            neg_facts = (-n for n in pos_facts)
            alp = alphaz(self)[0]
            roots = []

            for p,n in zip(pos_facts,neg_facts):
                rem = self.solve_for(**{alp : p})
                if rem == 0:
                    roots.append(p)

                rem = self.solve_for(**{alp : n})
                if rem == 0:
                    roots.append(n)

            return roots
        else: return [0]

    zeroes = roots


    def __repr__(self) -> Algebra:
        '''docstring'''
        return str(self.eq)

# 'common' func to be programmed...
# def solve(*eqns): ...To be programmed for solving linear equaions in multy vars.

'''
import matplotlib.pyplot as plt
import numpy as np

# Plot diagonal line (45 degrees)
h = plt.plot(np.arange(0, 10), np.arange(0, 10))

# set limits so that it no longer looks on screen to be 45 degrees
plt.xlim([-10, 20])

# Locations to plot text
l1 = np.array((1, 1))
l2 = np.array((5, 5))

# Rotate angle
angle = 45
trans_angle = plt.gca().transData.transform_angles(np.array((45,)),
                                                   l2.reshape((1, 2)))[0]

# Plot text
th1 = plt.text(l1[0], l1[1], 'text not rotated correctly', fontsize=16,
               rotation=angle, rotation_mode='anchor')
th2 = plt.text(l2[0], l2[1], 'text rotated correctly', fontsize=16,
               rotation=trans_angle, rotation_mode='anchor')

plt.show()
'''
