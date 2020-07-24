from Crypto.Util.number import *
#from pwn import *
import random
# import requests
import socket
import base64
import copy
import requests
#import ed25519
import json
from Crypto.Cipher import AES
from Crypto.PublicKey import RSA
from Crypto.Util.Padding import pad, unpad
from sympy.ntheory import *
from sympy.ntheory.modular import *
#from randcrack import RandCrack
import numpy
import re
import sys
import base65536
import gzip
import math
import zlib
#import gmpy2
from urllib.parse import urlencode
from sympy import Poly
#from sympy.abc import x
from sympy.core.numbers import Integer
from sympy import *
import itertools
from sympy.solvers.solveset import *
import string
from cryptography.hazmat.primitives.serialization import load_pem_public_key, load_pem_private_key
from cryptography.hazmat.primitives.asymmetric import rsa, padding, utils
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import hashes
from cryptography.exceptions import InvalidSignature
from sympy.ntheory.primetest import isprime
from sympy.core.compatibility import as_int

def isprimary(n):
    return n.imag % 2 == 0 and (n.real + n.imag) % 4 == 1

def isirreducible(n):
    if (n.real**2 == 1 and n.imag**2 == 1):
        return True
    elif (n.real % 4 == 3 and isprime(n.real) and n.imag == 0):
        return True
    elif(n*n.conjugate() % 4 == 1 and isprime(n*n.conjugate())):
        return True
    return False

def perfectsq (n):
    return int(math.sqrt(n))**2 == n

def brute2square(n):
    est = int(math.sqrt(n))
    sign = 1
    inc = 0
    while(True):
        a = est-sign*inc
        #print(a)
        if (perfectsq(n - a**2)):
            return a, int(math.sqrt(n-a**2))
        if (sign == -1):
            inc += 1
        sign *= -1


sieve.extend(14)
# print(sieve)


def generate_basis(n):
    basis = [True] * n
    for i in range(3, int(n**0.5)+1, 2):
        if basis[i]:
            basis[i*i::2*i] = [False]*((n-i*i-1)//(2*i)+1)
    return [2] + [i for i in range(3, n, 2) if basis[i]]


def miller_rabin(n, basis):
    """
    Miller Rabin test testing over all
    prime basis < b
    """
    # basis = generate_basis(b)
    if n == 2 or n == 3:
        return True

    if n % 2 == 0:
        return False

    r, s = 0, n - 1
    while s % 2 == 0:
        r += 1
        s //= 2
    for b in basis:
        x = pow(b, s, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def coquot(a, b):
    q = (a / b)
    return complex(round(q.real), round(q.imag))

def comodulo(a, b):
    q = coquot(a, b)
    return a - q*b

def removeramified(a):
    g1 = a
    inc = 0
    while((g1.real + g1.imag) % 2 == 0):
        g1 = g1/(1+1j)
        inc += 1
        #print('REMOVING {}'.format(g1))
    #print('REMOVED {}'.format(g1))
    return g1, inc

def xgcdgauss(a, b):
    s = 0
    t = 1
    r = b
    s1 = 1
    t1 = 0
    r1 = a
    while not (r == 0):
        q = coquot(r1, r)
        r1, r = r, r1-q*r
        s1, s = s, s1-q*s
        t1, t = t, t1-q*t
        #print(r1, s1, t1)
    return (r1, s1, t1)

def quarticres(a, b):
    #print(a, b)
    if (a == 1 or b == 1):
        return 1
    # if (a == -1):
    #     return (-1)**((b.real-1)//2)
    if not isprimary(b):
        new_b = b
        for i in range(3):
            new_b *= 1j
            if (isprimary(new_b)):
                return quarticres(a, new_b)
    g1 = comodulo(a, b)
    if (g1 == 0):
        return 0
    g2, m = removeramified(g1)
    #g3 = Complex(g2.re(), g2.im())
    c = 0
    for n in range(4):
        g3 = (g2 / 1j ** n)
        if (isprimary(g3)):
            c = n
            break
    #print('VALID {} {}'.format(isprimary(g3), g3))
    #print('{} N'.format(n))
    return 1j**(m*(b.real-b.imag-b.imag**2-1)/4 - c*(b.real-1)/2)*(-1)**((g3.real-1)*((b.real-1)/4))*quarticres(b, g3)
def comodinv(a, m):
    if (a.real == m):
        d = inverse(-1 * ((a.real) ** 2 * inverse(a.imag, m) + a.imag), m) % m
        c = -1 * d * a.real * inverse(a.imag, m)
        return complex(c, d)
    c = inverse(a.real + a.imag**2*inverse(a.real, m), m)
    d = (-1*a.imag*c*inverse(a.real, m)) % m
    return complex(c, d)

def roundc (a):
    return complex(int(round(a.real)), int(round(a.imag)))

R = [[1, 5+4j]]
#print(sieve._list[1:])`
prod = 1
for b in sieve._list[1:]:
    prod *= b
    #b = Complex(b, 0)
    temp = []
    #print(b.re() % 4)
    print(b)
    if (b % 4 == 3):
        for x in range(1, 4*b, 4):
            for y in range(0, 4*b, 4):
                #print(x, y)
                alpha = complex(x, y)
                palpha = (alpha*alpha.conjugate()+1)/2
                #print('{} PALPHA'.format(palpha))
                #print(quarticres(alpha, b))
                #print(quarticres(palpha, b))
                res = quarticres(alpha, b)
                #print('{} TEST VALUE'.format(alpha))
                # if (not res.im() == 0):
                #     res = Complex(-1, 0)
                #print(res, legendre_symbol(int(palpha.real), b))

                if(res == legendre_symbol(int(palpha.real), b)):
                    temp.append(alpha)

    else:
        beta = brute2square(b)
        beta = complex(beta[0], beta[1])
        for x in range(1, 4*b, 4):
            for y in range(0, 4*b, 4):
                alpha = complex(x, y)
                if (comodinv(alpha, b) == 0):
                    continue
                palpha = (alpha * alpha.conjugate() + 1) / 2
                #print(quarticres(alpha*comodinv(alpha, b).conj(), b))
                if(quarticres(alpha*comodinv(alpha, b).conjugate(), beta) == legendre_symbol(int(palpha.real), b)):
                    temp.append(alpha)
    print([str(x) for x in temp])
    R.append(temp)

prod *= 2*4
print(R)
for a in R:
    print(len(a))
#print(Complex(1, 1)**3)
#print(quarticres(5, 3))
print(legendre_symbol(25+64, 11))
print((1+1j)**0.5)
arr = []
gcd = 1
pointer = 0
#print(comodinv(13+4j, 13))

#print((int(math.sqrt(math.sqrt(8*2**600))) + 1000*prod)**4/8 - 2**600)
#print(int(math.sqrt(math.sqrt(8*(2**600))))//prod-int(math.sqrt(math.sqrt(8*2**600)))//prod)
basis = generate_basis(14)
#sum = 14501 + 107580j
m = 120120
R2 = []
# with open('RAINBOW3', 'w') as f:
#     for x in range(1, m, 4):
#         for y in range(0, m, 60):
#             #print(x, y)
#             failure = False
#             for i, p in enumerate(sieve._list):
#                 #print(complex(x % (4*p), y % (4*p)), 4*p)
#                 #print('MOD {} {}'.format(y % (4*p), p))
#                 if (complex(x % (4*p), y % (4*p)) not in R[i]):
#                     failure = True
#                     break
#             if not failure:
#                 R2.append(complex(x, y))
#                 f.write('{} {}\n'.format(x, y))
with open('prime_precalc', 'w') as f:
    for tup in itertools.product(R[0], R[1], R[2], R[3], R[4], R[5]):
        sum = 0
        for i, p in enumerate(sieve._list):
            base = 4*p
            sum += tup[i]*m/base*inverse(m/base, base)
        sum = complex(sum.real % m, sum.imag % m)
        R2.append(sum)
        f.write('{} {}\n'.format(int(sum.real), int(sum.imag)))
print(R2)
# with open('RAINBOW3') as f:
#     for l in f:
#         l2 = l.split(' ')
#         R2.append(complex(int(l2[0]), int(l2[1])))

print(len(R2))
#sum = complex(sum.real % m, sum.imag % m)
#print(sum)
print(basis)
#print(int(math.sqrt(math.sqrt(8*(10**24))))//m)
break_loop = False
for sum in R2:
    for u in range(int(math.sqrt(math.sqrt(8*(2**600))))//m, int(math.sqrt(math.sqrt(8*(2**600))))//m + 1000):
        for v in range(0, int(math.sqrt(math.sqrt(8*(2**600))))//m + 1000 - u):
            q = int((sum.real+u*m)**2 + (sum.imag+v*m)**2)
            #print(q)
            p = (q+1)//2
            n = p*q
            #print(n)
            if (miller_rabin(n, basis)):
                print("PSEUDO: {}".format(n))
                break_loop = True
                break
            q = int((sum.real - u * m) ** 2 + (sum.imag + v * m) ** 2)
            #print(q)
            p = (q + 1) // 2
            n = p * q
            #print(n)
            if (miller_rabin(n, basis)):
                print("PSEUDO: {}".format(n))
                break_loop = True
                break
        if (break_loop):
            break

#print(gcd)
# product = 1
# for i in range(len(arr)):
#     product *= R[i][arr[i]]
# print(product)
# print(is_nthpow_residue(5 % 3, 4, 3))
# print(is_nthpow_residue(5 % 3, 2, 3))
#print(quarticres(complex(1, 3), complex(7, 2)) == quarticres(complex(7, 2), complex(1, 3)))
# for i in range(4):
#     n = (-1-2j)/1j**i
#     print(n, isprimary(n))
# print(brute2square(13))
# print(xgcdgauss(2+4j, 13))
# print((-4-5j)*(2+4j) + (-1+2j)*13)
# print(2**600)
# print(2**900)
