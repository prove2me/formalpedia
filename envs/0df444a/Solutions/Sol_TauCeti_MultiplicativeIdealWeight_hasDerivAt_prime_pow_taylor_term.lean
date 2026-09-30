-- Prove2me | solution 1 for TauCeti.MultiplicativeIdealWeight.hasDerivAt_prime_pow_taylor_term
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:15.604006+00:00
-- url     : https://prove2.me/submissions/0834d118-fbd1-4a5d-b868-4ee10aebd911

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Regrouping an ideal-indexed Dirichlet series by absolute norm

An `TauCeti.IdealArithmeticFunction K` has two Dirichlet series attached to it: the series indexed
by the nonzero integral ideals of `𝓞 K`, whose terms are `TauCeti.idealTerm`, and the Mathlib
`LSeries` of the regrouped coefficients `TauCeti.normCoeff`. This file proves that the second is
obtained from the first by summing over the finite absolute-norm fibres, so that absolute
convergence of the ideal-indexed series transfers to the `LSeries` together with the value of the
sum.

## Main definitions

* `TauCeti.idealTerm f s I` is the term `f I / N(I) ^ s` of the ideal-indexed Dirichlet series.
* `TauCeti.idealAbscissaOfAbsConv f` is the abscissa of absolute convergence of that series, the
  ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`.

## Main results

* `TauCeti.regroupByNorm`: if the ideal-indexed series has sum `L` at `s`, then so does the
  `LSeries` of `TauCeti.normCoeff f`; `TauCeti.LSeriesSummable_normCoeff` and
  `TauCeti.LSeries_normCoeff` are the summability and value statements it packages.
* `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`: weighting the ideal terms
  by `log N(I)` keeps them summable strictly to the right of a point of absolute convergence.
* `TauCeti.abscissaOfAbsConv_normCoeff_le`: consequently the grouped abscissa of absolute
  convergence is at most the ideal-indexed one.
* `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm`: the converse holds whenever no
  cancellation occurs inside a norm fibre. `TauCeti.summable_idealTerm_of_nonneg` and
  `TauCeti.idealAbscissaOfAbsConv_eq_abscissaOfAbsConv` specialize it to the case where every
  *individual ideal summand* is nonnegative, where moreover the two abscissae agree.

## Implementation notes

The regrouping is an instance of Mathlib's `HasSum.tsum_fiberwise` along the absolute norm
`fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))`, whose fibres are the finite sets
`TauCeti.normFiber K n`. Absolute convergence of the ideal-indexed series is expressed as plain
`Summable`, which for a complex-valued family is unconditional convergence and hence absolute
convergence; no rearrangement hypothesis is therefore needed for the transfer.

The converse is proved through `summable_partition` applied to the norms of the terms. All it
needs about `f` is that the norm of each grouped coefficient is the sum of the norms over its
fibre — the absence of cancellation inside the fibre. Nonnegativity of every ideal summand is one
way to secure that, through `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`; it is the step that
fails under cancellation, as the rejection test
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` records. That test is a statement about
`TauCeti.normCoeff` alone, so it lives with that definition rather than here.

## Roadmap role

This is Layer **1.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the required worked
example 9 accompanies it in `TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean`. The
exact value of the abscissa for the trivial weight is deliberately not proved here: its divergence
input is the Layer 5 ideal count of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)











/-! ### Regrouping -/











/-! ### The ideal-indexed abscissa of absolute convergence -/













/-! ### The converse, in the absence of cancellation inside norm fibres -/











end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Canonical local factors and formal Euler products for ideal arithmetic functions

This file develops the Euler-product layer for arithmetic functions on nonzero ideals. It builds
the canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

It then restricts an ideal arithmetic function to the nonzero ideals whose prime factors lie in a
prescribed set of height-one primes, and proves that for a *finite* set of primes the norm
coefficients of that restriction are exactly the product of the local factors, taken in Mathlib's
Dirichlet convolution of arithmetic functions. Passing to Mathlib's formal Euler product gives the
norm coefficients of the original function. Everything here is a formal identity of coefficients:
no analytic convergence hypothesis enters.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.IdealArithmeticFunction.supportedPart f S` is `f` restricted to the nonzero ideals all
  of whose prime factors lie in `S`, and zero elsewhere.

## Main results

* `TauCeti.IdealArithmeticFunction.supportedPart_insert`: for a multiplicative `f`, adjoining one
  prime to the support convolves the restriction with the restriction to the powers of that prime.
* `TauCeti.IdealArithmeticFunction.normCoeff_supportedPart`: the **finite Euler product**
  `normCoeff (supportedPart f S) = ∏ P ∈ S, localArithmeticFactor f P` for a multiplicative `f`
  and a finite set `S` of height-one primes.
* `TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct`: the norm coefficients of a
  multiplicative ideal arithmetic function are Mathlib's formal Euler product of its canonical
  local factors.

## Implementation notes

"Supported on `S`" is spelled `Ideal.IsPrimeTo · Sᶜ`: no prime *outside* `S` divides the ideal.
That predicate, and the splitting `Ideal.IsPrimeTo.exists_eq_pow_mul` of an ideal into a prime
power times a cofactor together with its uniqueness `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul`, live
in `TauCeti/RingTheory/DedekindDomain/Ideal.lean`, since nothing in them is specific to a number
field. Uniqueness is what makes the induction work: it is why exactly one summand of the ideal
convolution survives at each ideal. The multiplicativity of `f` over a prime-power factorization,
`TauCeti.IdealArithmeticFunction.IsMultiplicative.map_prod_pow`, likewise lives with the predicate
it elaborates, in `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`.

`TauCeti.MultiplicativeIdealWeight.restrict` is the opposite regime and is not a substitute:
it restricts *away from* a **finite** set of primes and stays inside the bundled weight carrier. A
finite Euler product needs support on a *finite* set of primes, so all but finitely many primes are
bad; such a function is never a `MultiplicativeIdealWeight`, whose zero support is finite by
definition. Hence `supportedPart` is a plain ideal arithmetic function.

Finiteness is what carries the finite products to the full Euler product. A nonzero ideal has
only finitely many prime divisors, and only finitely many primes have norm at most a given `n`, so
at a fixed norm coefficient the restriction `supportedPart f S` already agrees with `f` as soon as
`S` contains those primes. Each finite product is therefore eventually the exact norm coefficient,
and Mathlib's `ArithmeticFunction.eulerProduct`, being the limit of those finite products, computes
the norm coefficients of `f` itself. The local factors are derived from `f` rather than stored, so
this identity holds for any multiplicative `f` with no further data.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose local-factor target signatures
  and naming are adapted here.
-/

 section

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K]



/-- A prime power, as a nonzero integral ideal, has the expected underlying ideal. -/
@[simp]
theorem coe_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (primeIdealPow P e : Ideal (𝓞 K)) = P.asIdeal ^ e :=
  (rfl)

variable [NumberField K]

/-- The absolute norm is multiplicative on prime powers. -/
theorem absNorm_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    Ideal.absNorm (primeIdealPow P e : Ideal (𝓞 K)) = Ideal.absNorm P.asIdeal ^ e := by
  rw [coe_primeIdealPow, map_pow]





end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]



























/-! ### Finite Euler products -/



variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}































end IdealArithmeticFunction

end TauCeti

end
end

section
set_option autoImplicit true
namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The analytic Euler product of an ideal arithmetic function

`TauCeti.EulerProductData.normCoeff_eq_eulerProduct` identifies the norm coefficients of bundled
Euler-product data with a formal Euler product, coefficient by coefficient. This file supplies the
analytic statement it does not: where the Dirichlet series indexed by the nonzero ideals converges
absolutely, the infinite product of the local Euler factors converges, in the unrestricted sense
of `HasProd` over the height-one primes, to the `LSeries` of the norm coefficients.

The local factor at a height-one prime `P` is the `LSeries` of the canonical local arithmetic
factor, equivalently the prime-power Dirichlet series `∑' e, f (P ^ e) / N(P ^ e) ^ s`. For a
completely multiplicative weight that series is geometric, and the factor takes the familiar
closed form `(1 - χ(P) N(P) ^ (-s))⁻¹`; specializing to the trivial weight gives the Euler
product of the Dedekind zeta function.

## Main definitions

* `TauCeti.EulerProductData.eulerFactor`: the local Euler factor at a height-one prime.

## Main results

* `TauCeti.EulerProductData.hasProd_eulerFactor`: the **analytic Euler product**, when the
  ideal-indexed Dirichlet series converges absolutely at `s`.
* `TauCeti.EulerProductData.norm_absNorm_cpow_neg_le_radius_localPowerSeries`: a lower bound for
  the convergence radius of a local power series from absolute convergence at a real point.
* `TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor`: the same product, with the local factors
  in the closed geometric form available for a completely multiplicative weight.
* `TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm`: the `L`-series is
  **nonzero** wherever the ideal-indexed series converges absolutely.
* `TauCeti.dedekindZeta_eulerProduct_hasProd`: the **Euler product of the Dedekind zeta
  function**, valid on `Re s > 1`.
* `TauCeti.dedekindZeta_ne_zero_of_one_lt_re`: the Dedekind zeta function is **nonzero** on
  `Re s > 1`.
* `IsDedekindDomain.HeightOneSpectrum.one_lt_norm_absNorm_cpow` and
  `IsDedekindDomain.HeightOneSpectrum.absNorm_cpow_sub_one_ne_zero`: analytic bounds for the
  complex powers of prime-ideal norms on the right half-plane.
* `IsDedekindDomain.HeightOneSpectrum.logDeriv_one_sub_absNorm_cpow_neg`: the logarithmic
  derivative of a deleted Euler factor.

The nonvanishing is pointwise, at each `s` where the ideal-indexed series converges absolutely, and
nothing is claimed off that region. It is not a formality: an unconditionally convergent product of
nonzero factors may still vanish.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `EulerProduct` API, whose `Nat.Primes`-indexed statements this file mirrors for the
  height-one primes of a number field.
-/

 section

open scoped _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]











end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}

/-! ### The local Euler factor -/







end EulerProductData

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

/-! ### Restriction to a set of primes, analytically -/















end IdealArithmeticFunction

namespace EulerProductData

open _root_.TauCeti.IdealArithmeticFunction

variable (D : EulerProductData K) {s : ℂ}













/-! ### The infinite Euler product -/







end EulerProductData

/-! ### Completely multiplicative weights -/

namespace MultiplicativeIdealWeight

open _root_.TauCeti.IdealArithmeticFunction

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- The ideal terms of a completely multiplicative weight along the powers of a prime form a
geometric progression. -/
@[simp]
theorem idealTerm_toIdealArithmeticFunction_primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (s : ℂ) :
    idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow e) =
      (χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ e := by
  rw [idealTerm_def, toIdealArithmeticFunction_apply,
    P.absNorm_primeIdealPow, P.coe_primeIdealPow,
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, div_pow]













end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function -/







end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Derivatives of ideal-indexed Dirichlet series

Differentiating an ideal term `idealTerm K f s I = f I / N(I) ^ s` in `s` returns the same term
weighted by `-log N(I)`.  Summing over the nonzero integral ideals, the derivative of the
norm-regrouped `L`-series is therefore, up to a sign, the ideal-indexed Dirichlet series of the
*logarithmic weighting* `TauCeti.IdealArithmeticFunction.logMul` of `f`, the pointwise product of
`f` with `log N(I)`.

This file proves that identity, its iterated form, and the resulting expression of the logarithmic
derivative as a quotient of two ideal-indexed sums.  The norm-regrouped derivative, its iterated
form, and the logarithmic-derivative result assume that `s` lies strictly to the right of
`TauCeti.idealAbscissaOfAbsConv K f`, the abscissa of absolute convergence of the ideal-indexed
series; the logarithmic weight can destroy summability on the boundary line itself, which is why
a point of convergence strictly to the left is what the estimates consume.

Two facts do the work.  Regrouping by absolute norm turns `logMul` into Mathlib's `LSeries.logMul`,
because the weight `log N(I)` is constant on a norm fibre
(`TauCeti.normCoeff_logMul`); and a logarithmic weight leaves the ideal-indexed series summable
strictly to the right of any point of absolute convergence
(`TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`).  Mathlib's `LSeries_hasDerivAt`
then supplies the calculus, and `TauCeti.regroupByNorm` converts its conclusion back to a sum over
ideals.

## Main definitions

* `TauCeti.IdealArithmeticFunction.logMul`: the pointwise product of an ideal arithmetic function
  with `log N(I)`, the ideal-indexed counterpart of Mathlib's `LSeries.logMul`.  Its `m`-fold
  iterate weights by `log N(I) ^ m` (`TauCeti.IdealArithmeticFunction.logMul_iterate_apply`).

## Main results

* `TauCeti.hasDerivAt_idealTerm`: the derivative in `s` of an ideal term is the term itself,
  weighted by `-log N(I)`.
* `TauCeti.normCoeff_logMul`: regrouping by absolute norm carries the ideal-indexed logarithmic
  weight to Mathlib's.
* `TauCeti.summable_idealTerm_logMul_of_re_lt_re`: a logarithmic weight preserves absolute
  convergence strictly to the right.
* `TauCeti.IdealArithmeticFunction.hasDerivAt_LSeries_normCoeff` and
  `TauCeti.IdealArithmeticFunction.deriv_LSeries_normCoeff`: the derivative of the regrouped
  `L`-series is `-∑ I, log N(I) f I N(I) ^ (-s)`, summed over the nonzero integral ideals.
* `TauCeti.IdealArithmeticFunction.iteratedDeriv_LSeries_normCoeff`: the `m`-th derivative, with
  the weight `log N(I) ^ m`.
* `TauCeti.IdealArithmeticFunction.logDeriv_LSeries_normCoeff`: the logarithmic derivative as the
  quotient of the two ideal-indexed sums.
* `TauCeti.IdealArithmeticFunction.differentiableOn_LSeries_normCoeff`: absolute convergence of
  an ideal-indexed series throughout an open set makes its norm-regrouped `L`-series holomorphic
  there.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

 section

namespace TauCeti

open Complex

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **The derivative of an ideal term.**  Differentiating `f I / N(I) ^ s` in `s` returns the same
term weighted by `-log N(I)`.

Differentiating a sum of ideal terms termwise needs this at each term.  The logarithm is the
complex one, of a positive real argument: `N(I) ≥ 1` for a nonzero ideal, so it agrees with
`Real.log N(I)` and is real and nonnegative. -/
theorem hasDerivAt_idealTerm (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) (s : ℂ) :
    HasDerivAt (fun z ↦ idealTerm K f z I)
      (-(Complex.log (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) * idealTerm K f s I)) s := by
  have hn : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 :=
    (Ideal.absNorm_pos_of_nonZeroDivisors I).ne'
  -- An ideal term is the `L`-series term of the constant coefficient `f I` at `N(I)`, so
  -- Mathlib's `LSeries.hasDerivAt_term` already does the calculus.
  have h := LSeries.hasDerivAt_term (fun _ ↦ f I) (Ideal.absNorm (I : Ideal (𝓞 K))) s
  simp only [LSeries.term_of_ne_zero hn, LSeries.logMul] at h
  simpa [idealTerm_def, mul_div_assoc] using h

/-! ### The logarithmic weighting -/

namespace IdealArithmeticFunction

variable {K}







end IdealArithmeticFunction

open IdealArithmeticFunction













namespace IdealArithmeticFunction

/-! ### Differentiating the regrouped `L`-series -/











end IdealArithmeticFunction

end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Derivatives of ideal Euler factors and logarithmic expansions

For general `TauCeti.EulerProductData`, this file first differentiates each local Euler factor.
The derivative at a prime `P` is the exact prime-power series

`-∑ e, log N(P ^ e) · D(P ^ e) / N(P ^ e) ^ s`.

This is the local analytic input for expressing the logarithmic derivative of a general ideal
Euler product in terms of its prime-power data. The second part of the file specializes to a
completely multiplicative weight, where the logarithm itself has a geometric Taylor expansion and
can be differentiated after summing over all primes and exponents.

`TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub` expands the sum of local
logarithms over the prime powers `(P, e)`.  This file differentiates that expansion in `s`, term by
term, on the open half-plane where the ideal-indexed series converges absolutely.

Each term `(χ(P) N(P)⁻ˢ) ^ (e+1) / (e+1)` differentiates to `-log N(P) * (χ(P) N(P)⁻ˢ) ^ (e+1)`, so
the differentiated family is the undivided one weighted by `-log N(P)`.  Termwise differentiation of
a sum needs a summable majorant valid across a neighbourhood rather than at the single point, and
the half-plane supplies it: strictly to the right of a point of absolute convergence the weight
`log N(P)` is absorbed, which is `summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`, and the
exponent direction is geometric, which is `TauCeti.summable_mul_norm_pow_succ`.

`EulerProduct/Branch.lean` identifies the derivative of a *branch* of the logarithm with the
logarithmic derivative of the `L`-series.  That is an abstract identification; this file gives the
prime-power series the derivative is equal to.

## Main results

* `TauCeti.EulerProductData.hasDerivAt_eulerFactor`: a general local Euler factor differentiates
  termwise into the negative of its log-weighted prime-power series.
* `TauCeti.EulerProductData.logDeriv_eulerFactor_eq`: the local factor's logarithmic derivative is
  the negative quotient of that prime-power series by the local factor.
* `TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_prime_pow`: the prime-power expansion
  differentiates termwise, strictly right of the abscissa of absolute convergence.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_tsum_prime_pow`: that derivative **is**
  the logarithmic derivative of the `L`-series.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Complex IsDedekindDomain

open scoped nonZeroDivisors NumberField

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (D : EulerProductData K)

/-! ### Derivative of a general local Euler factor -/











end EulerProductData

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- **The Taylor term at `(P, e)` differentiates to `-log N(P)` times the undivided power.**  The
division by `e + 1` is what makes the derivative the plain power rather than a multiple of it. -/
theorem solution (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    _root_.HasDerivAt (fun z : ℂ ↦ (χ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1)
        / ((e : ℂ) + 1))
      (-(_root_.Complex.log (_root_.Ideal.absNorm P.asIdeal : ℂ)
        * (χ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (e + 1))) s := by
  have hne : ((e : ℂ) + 1) ≠ 0 := by
    have : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast _root_.Nat.succ_ne_zero e
  have hterm : ∀ z : ℂ, (χ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ z) ^ (e + 1)
      = _root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction z (P.primeIdealPow (e + 1)) := fun z ↦
    (_root_.TauCeti.MultiplicativeIdealWeight.idealTerm_toIdealArithmeticFunction_primeIdealPow χ P (e + 1) z).symm
  have hlog : _root_.Complex.log ((_root_.Ideal.absNorm ((P.primeIdealPow (e + 1) : (_root_.Ideal (𝓞 K))⁰) :
        _root_.Ideal (𝓞 K))) : ℂ)
      = ((e : ℂ) + 1) * _root_.Complex.log (_root_.Ideal.absNorm P.asIdeal : ℂ) := by
    rw [P.absNorm_primeIdealPow, ← _root_.Complex.natCast_log, ← _root_.Complex.natCast_log]
    push_cast [_root_.Real.log_pow]
    ring
  have hval : -(_root_.Complex.log (_root_.Ideal.absNorm P.asIdeal : ℂ)
        * _root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow (e + 1)))
      = -(_root_.Complex.log ((_root_.Ideal.absNorm ((P.primeIdealPow (e + 1) : (_root_.Ideal (𝓞 K))⁰) :
            _root_.Ideal (𝓞 K))) : ℂ)
          * _root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction s (P.primeIdealPow (e + 1)))
        / ((e : ℂ) + 1) := by
    rw [hlog]
    field_simp
  simp_rw [hterm]
  rw [hval]
  exact (_root_.TauCeti.hasDerivAt_idealTerm K χ.toIdealArithmeticFunction
    (P.primeIdealPow (e + 1)) s).div_const ((e : ℂ) + 1)









end MultiplicativeIdealWeight

end TauCeti

end
end
