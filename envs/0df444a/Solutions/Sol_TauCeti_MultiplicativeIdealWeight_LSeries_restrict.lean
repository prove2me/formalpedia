-- Prove2me | solution 1 for TauCeti.MultiplicativeIdealWeight.LSeries_restrict
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:01:36.751025+00:00
-- url     : https://prove2.me/submissions/a3d7b688-2edb-4c09-84d6-a01a1fb5df7b

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Analytic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Basic
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
import Theorems.Thm_TauCeti_EulerProductData_LSeries_restrictAway_mul_prod_eulerFactor
import Theorems.Thm_TauCeti_EulerProductData_eulerFactor_eq_tsum
import Theorems.Thm_TauCeti_EulerProductData_restrictAway_apply

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
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Euler-product coefficient data over a number field

This file bundles the algebraic input for an Euler product over the height-one primes of the ring
of integers of a number field. An `EulerProductData K` consists of an ideal arithmetic function
that is multiplicative on relatively prime nonzero ideals. The prime-power series and local
arithmetic factors are canonically derived from the function as defined in
`EulerProduct/Basic.lean`, so nothing about the local behaviour is stored: the bundle carries
exactly the one algebraic hypothesis that an Euler product consumes.

The formal Euler-product identity follows from
`IdealArithmeticFunction.normCoeff_eq_eulerProduct`: coprime multiplicativity and unique
factorization prove that `normCoeff` is Mathlib's `ArithmeticFunction.eulerProduct` of the
canonical local factors.

Two hypotheses of the classical theory are deliberately absent, because the identity proved here
does not need either. There is no distinguished finite set of exceptional primes: multiplicativity
is required on every coprime pair of nonzero ideals, and the local factor at a prime is read off
from the coefficients at its powers, good or bad. There is also no analytic input: the identity is
an equality of arithmetic functions, and the convergence of the evaluated factors to an infinite
product is a separate question.

## Main definitions

* `TauCeti.EulerProductData` bundles a multiplicative ideal coefficient system.
* `TauCeti.EulerProductData.ofMultiplicativeIdealWeight` regards a degree-one ideal weight as
  Euler-product data.
* Pointwise multiplication, complex conjugation, and restriction away from sets of primes
  preserve the bundle.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)



namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]



























/-- The coefficient function underlying the Euler-product data of a multiplicative ideal weight. -/
@[simp]
theorem toIdealArithmeticFunction_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K) :
    (ofMultiplicativeIdealWeight χ).toIdealArithmeticFunction = χ.toIdealArithmeticFunction := by
  funext I
  rfl





















end EulerProductData

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



/-- Absolute convergence puts every local ratio `χ(P) N(P)⁻ˢ` strictly inside the unit disc, so no
local Euler factor has a vanishing denominator. -/
theorem one_sub_div_ne_zero_of_summable_idealTerm
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) (P : HeightOneSpectrum (𝓞 K)) :
    1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s ≠ 0 := fun h ↦ by
  have hlt := norm_div_lt_one_of_summable_idealTerm χ hs P
  rw [sub_eq_zero] at h
  rw [← h] at hlt
  simp at hlt

/-- The local Euler factor of a completely multiplicative weight is the geometric closed form
`(1 - χ(P) N(P)⁻ˢ)⁻¹`. -/
theorem eulerFactor_ofMultiplicativeIdealWeight
    (P : HeightOneSpectrum (𝓞 K))
    (hP : ‖χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1) :
    (EulerProductData.ofMultiplicativeIdealWeight χ).eulerFactor P s =
      (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)⁻¹ := by
  rw [EulerProductData.eulerFactor_eq_tsum,
    EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight,
    tsum_congr fun e ↦ idealTerm_toIdealArithmeticFunction_primeIdealPow χ P e s]
  exact tsum_geometric_of_norm_lt_one hP





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
# Deleting finitely many Euler factors

Restricting Euler-product data away from a finite set `S` of primes, keeping only the
coefficients of the ideals prime to `S`, replaces the local Euler factors at `S` by `1` and leaves
the others untouched. On the half-plane of absolute convergence the two `L`-series therefore
differ by the finitely many deleted factors; for a completely multiplicative weight `χ` the
restriction `χ.restrict S` divides the `L`-series by `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))⁻¹`.

For the trivial weight the restriction is `ofBadPrimes S`, the indicator of the ideals prime to
`S`, and its `L`-series is the Dedekind zeta function with the Euler factors at `S` removed:

`L_S(s) = ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`  for `Re s > 1`.

The correction factor does not vanish on `Re s > 0`, because
`|N(𝔭) ^ s| = N(𝔭) ^ (Re s) > 1` there. As `s → 1⁺`, the normalized expression
`(s - 1) L_S(s)` tends to `dedekindZeta_residue K` multiplied by the nonzero number
`∏ 𝔭 ∈ S, (1 - N(𝔭)⁻¹)`. The logarithmic derivative of `L_S` differs from that of `ζ_K` by the
finite sum `∑ 𝔭 ∈ S, log N(𝔭) / (N(𝔭) ^ s - 1)`, which is holomorphic on `Re s > 0` and in
particular across the line `Re s = 1`. This is the form in which Dirichlet series whose Euler
products omit the ramified primes, such as the trivial Galois-character series, are compared with
`ζ_K`.

## Main results

* `TauCeti.EulerProductData.eulerFactor_restrictAway_of_mem`,
  `TauCeti.EulerProductData.eulerFactor_restrictAway_of_notMem`: restricting away from `S`
  replaces the local factors at `S` by `1` and keeps the others.
* `TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor`: multiplying the `L`-series
  of the restriction by the deleted local factors recovers the original `L`-series.
* `TauCeti.MultiplicativeIdealWeight.LSeries_restrict`: the same for a completely multiplicative
  weight, with the deleted factors in closed form.
* `TauCeti.LSeries_ofBadPrimes`: the `L`-series of the indicator of the ideals prime to `S` is
  `ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))` on `Re s > 1`.
* `TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero`: the correction factor has no zero on
  `Re s > 0`.
* `TauCeti.dedekindZeta_residue_mul_prod_one_sub_absNorm_cpow_neg_one_ne_zero`: the corrected
  residue at `s = 1` is nonzero.
* `TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes`: the normalized right-hand limit at `s = 1`.
* `TauCeti.logDeriv_LSeries_ofBadPrimes`: the logarithmic derivative on `Re s > 1`, and
  `TauCeti.differentiableOn_sum_log_absNorm_div_cpow_sub_one`: the correction term in it is
  holomorphic on `Re s > 0`.
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.LSeries_normCoeff` and
  `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.tendsto_sub_one_mul_LSeries`: a weight that
  is a norm twist with parameter `u` on its good ideals has for `L`-series such a deleted zeta
  function read at `s - u * I`, with the corresponding pole at `s = 1 + u * I`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

variable (D : EulerProductData K) {s : ℂ}









end EulerProductData

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- **Deleting finitely many Euler factors of a completely multiplicative weight.** Where the
ideal-indexed Dirichlet series of `χ` converges absolutely, restricting `χ` away from a finite set
`S` of primes multiplies its `L`-series by `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`, the reciprocal of the
deleted local factors. -/
theorem solution (S : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hs : _root_.Summable (_root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction s)) :
    _root_.LSeries (_root_.TauCeti.normCoeff K (χ.restrict S S.finite_toSet).toIdealArithmeticFunction) s =
      _root_.LSeries (_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction) s *
        ∏ P ∈ S, (1 - χ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ s) := by
  classical
  have hdata : _root_.TauCeti.EulerProductData.ofMultiplicativeIdealWeight (χ.restrict S S.finite_toSet) =
      (_root_.TauCeti.EulerProductData.ofMultiplicativeIdealWeight χ).restrictAway S :=
    _root_.TauCeti.EulerProductData.ext fun I ↦ by simp
  have key := _root_.TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor
    (_root_.TauCeti.EulerProductData.ofMultiplicativeIdealWeight χ) S (by simpa using hs)
  rw [← hdata, _root_.Finset.prod_congr _root_.rfl fun P _ ↦ _root_.TauCeti.MultiplicativeIdealWeight.eulerFactor_ofMultiplicativeIdealWeight χ P
    (_root_.TauCeti.MultiplicativeIdealWeight.norm_div_lt_one_of_summable_idealTerm χ hs P)] at key
  simp only [_root_.TauCeti.EulerProductData.toIdealArithmeticFunction_ofMultiplicativeIdealWeight] at key
  have hne : ∏ P ∈ S, (1 - χ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun P _ ↦ χ.one_sub_div_ne_zero_of_summable_idealTerm hs P
  rw [← key, _root_.Finset.prod_inv_distrib, _root_.mul_assoc, _root_.inv_mul_cancel₀ hne, _root_.mul_one]

end MultiplicativeIdealWeight

/-! ### The Dedekind zeta function with finitely many Euler factors deleted -/













/-! ### Weights that are norm twists on their good ideals -/

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight





end MultiplicativeIdealWeight

end TauCeti

end
end
