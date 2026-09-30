-- Prove2me | solution 1 for TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:38:48.875848+00:00
-- url     : https://prove2.me/submissions/a93f4933-5ef7-4996-8b69-ce7b794c6769

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
import Theorems.Thm_Complex_summable_taylorSeries_neg_log
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_hasDerivAt_prime_pow_taylor_term
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_norm_log_mul_prime_pow_le
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_summable_log_absNorm_mul_norm_prime_pow

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

/-- The absolute value of an ideal term depends on `s` only through its real part. -/
@[simp]
theorem norm_idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s I‖ = ‖f I‖ / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [idealTerm_def, norm_div,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I)]

/-- Ideal terms decrease in absolute value as the real part of `s` grows, because every nonzero
integral ideal has absolute norm at least one. -/
theorem norm_idealTerm_le_of_re_le_re (f : IdealArithmeticFunction K) {s s' : ℂ}
    (h : s.re ≤ s'.re) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s' I‖ ≤ ‖idealTerm K f s I‖ := by
  have h₁ : (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  have h₀ : (0 : ℝ) < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (by linarith) _
  simp only [norm_idealTerm]
  gcongr

/-- Absolute convergence of the ideal-indexed series propagates to the right. -/
theorem summable_idealTerm_of_re_le_re {f : IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re ≤ s'.re) (hf : Summable (idealTerm K f s)) : Summable (idealTerm K f s') := by
  rw [← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_idealTerm_le_of_re_le_re K f h)





/-! ### Regrouping -/











/-! ### The ideal-indexed abscissa of absolute convergence -/



/-- Defining equation of `TauCeti.idealAbscissaOfAbsConv`. -/
theorem idealAbscissaOfAbsConv_def (f : IdealArithmeticFunction K) :
    idealAbscissaOfAbsConv K f = sInf (Real.toEReal '' {x : ℝ | Summable (idealTerm K f x)}) :=
  (rfl)

/-- **A point of absolute convergence strictly to the left.**  Strictly to the right of the
ideal-indexed abscissa of absolute convergence there is a real point, still strictly to the left,
at which the ideal-indexed series converges absolutely.

This is the form in which the abscissa is consumed by estimates that need room to the left, such
as the logarithmic weights produced by differentiation. -/
theorem exists_summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re
    {f : IdealArithmeticFunction K} {s : ℂ} (hs : idealAbscissaOfAbsConv K f < s.re) :
    ∃ y : ℝ, Summable (idealTerm K f y) ∧ y < s.re := by
  simpa [idealAbscissaOfAbsConv, sInf_lt_iff] using hs

/-- The ideal-indexed series converges absolutely strictly to the right of its abscissa. -/
theorem summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) : Summable (idealTerm K f s) := by
  obtain ⟨y, hy, hys⟩ := exists_summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs
  exact summable_idealTerm_of_re_le_re K (Complex.ofReal_re y ▸ hys.le) hy





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

omit [NumberField K] in
/-- Distinct primes give distinct first powers, so a family indexed by the primes is a subfamily
of one indexed by the nonzero ideals. -/
theorem primeIdealPow_one_injective :
    Function.Injective fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealPow P 1 := fun P Q h ↦
  HeightOneSpectrum.asIdeal_injective
    (by simpa only [coe_primeIdealPow, pow_one] using
      congrArg (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)) h)

/-- Distinct exponents give distinct prime powers. -/
theorem primeIdealPow_injective (P : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (primeIdealPow P) := fun m n h ↦
  Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    (by simpa only [absNorm_primeIdealPow] using
      congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) h)

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













/-- **The prime terms are a subseries of the ideal terms.** Each height-one prime contributes its
own ideal as the `e = 1` member of its power series, and distinct primes give distinct ideals, so
absolute convergence over ideals restricts to the primes. Multiplicativity plays no part. -/
theorem summable_idealTerm_primeIdealPow_one (hs : Summable (idealTerm K f s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦ idealTerm K f s (P.primeIdealPow 1) :=
  hs.comp_injective HeightOneSpectrum.primeIdealPow_one_injective

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

/-- **The local ratio of a convergent weight is a contraction.** Absolute convergence of the
ideal-indexed Dirichlet series forces the geometric ratio at each prime to have modulus less than
one, because the powers of that prime already contribute a geometric subseries. -/
theorem norm_div_lt_one_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s))
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
  rw [← summable_geometric_iff_norm_lt_one]
  exact (hs.comp_injective P.primeIdealPow_injective).congr fun e ↦
    idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s

/-- **The local ratios are summable over the primes.** The multiplicative specialisation of
`IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one`: at a prime the ideal term *is* the
ratio `χ(P) N(P)⁻ˢ`. -/
theorem summable_div_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s :=
  (IdealArithmeticFunction.summable_idealTerm_primeIdealPow_one hs).congr fun P ↦ by
    simp [idealTerm_toIdealArithmeticFunction_primeIdealPow χ P 1 s]









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







/-- **The prime-power expansion differentiates termwise.**  Strictly to the right of the abscissa
of absolute convergence, the sum over prime powers is differentiable and its derivative is the
termwise one: the same family weighted by `-log N(P)`, with the division by `e + 1` gone.

The abscissa is all that is needed: convergence propagates rightward from any point to its left,
which is what supplies the majorant on a neighbourhood of `s`. -/
theorem solution {s : ℂ}
    (hs : _root_.TauCeti.idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    _root_.HasDerivAt (fun z : ℂ ↦ ∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1))
      (∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
        -(_root_.Complex.log (_root_.Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1))) s := by
  obtain ⟨s₀, hs₀, hs₀s⟩ : ∃ y : ℝ, _root_.Summable (_root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction y)
      ∧ y < s.re := by simpa [_root_.TauCeti.idealAbscissaOfAbsConv_def, _root_.sInf_lt_iff] using hs
  obtain ⟨σ₀, hσ₁₀, hσ₀s⟩ := _root_.exists_between hs₀s
  have hu : _root_.Summable fun pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ ↦
      _root_.Real.log (_root_.Ideal.absNorm pe.1.asIdeal)
        * ‖χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ (σ₀ : ℂ)‖ ^ (pe.2 + 1) :=
    χ.summable_log_absNorm_mul_norm_prime_pow (s := (s₀ : ℂ)) (s' := (σ₀ : ℂ))
      (by simpa using hσ₁₀) hs₀
  have hsum : _root_.Summable (_root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction s) :=
    _root_.TauCeti.summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K hs
  have hy₀ := _root_.Complex.summable_taylorSeries_neg_log
    (r := fun P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
      χ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ s)
    (χ.summable_div_of_summable_idealTerm hsum)
    (χ.norm_div_lt_one_of_summable_idealTerm hsum)
  exact _root_.hasDerivAt_tsum_of_isPreconnected
    (g := fun (pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ) (z : ℂ) ↦
      (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1))
    (g' := fun (pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ) (z : ℂ) ↦
      -(_root_.Complex.log (_root_.Ideal.absNorm pe.1.asIdeal : ℂ)
        * (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1)))
    (t := {z : ℂ | σ₀ < z.re}) (y₀ := s)
    hu (_root_.isOpen_lt _root_.continuous_const _root_.Complex.continuous_re)
    (_root_.convex_halfSpace_re_gt σ₀).isPreconnected
    (fun pe z _ ↦ χ.hasDerivAt_prime_pow_taylor_term pe.1 pe.2 z)
    (fun pe z hz ↦ χ.norm_log_mul_prime_pow_le pe.1 pe.2 (_root_.le_of_lt hz))
    hσ₀s hy₀ hσ₀s



end MultiplicativeIdealWeight

end TauCeti

end
end
