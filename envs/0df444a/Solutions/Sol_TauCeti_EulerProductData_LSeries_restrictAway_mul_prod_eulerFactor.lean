-- Prove2me | solution 1 for TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:56:02.819321+00:00
-- url     : https://prove2.me/submissions/d796b9a0-ea3f-4d74-af56-cf2e936bf325

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
import Theorems.Thm_TauCeti_EulerProductData_eulerFactor_eq_tsum
import Theorems.Thm_TauCeti_EulerProductData_hasProd_eulerFactor
import Theorems.Thm_TauCeti_EulerProductData_restrictAway_apply

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complements on ideals of a Dedekind domain

This file collects general facts about ideals and height-one primes of a Dedekind domain,
complementing `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`. In particular, it develops
the predicate `Ideal.IsPrimeTo I S`, saying that `I` is nonzero and divisible by no prime in `S`,
together with its induction principle `Ideal.IsPrimeTo.induction_on` and its transport
`Ideal.isPrimeTo_comap_iff` along a ring isomorphism.

The predicate is closed under products (`Ideal.isPrimeTo_mul_iff`, its finite form
`Ideal.isPrimeTo_prod_iff`) and powers (`Ideal.isPrimeTo_pow_iff`), and forbidding one more
prime is `Ideal.isPrimeTo_insert_iff`. Complementing a set of primes
turns it into a *support* condition: `IsPrimeTo I Sᶜ` says that every prime factor of `I` lies in
`S`. The two extreme cases are `Ideal.isPrimeTo_univ_iff` (no prime factor at all, so `I = ⊤`) and
`Ideal.isPrimeTo_compl_singleton_iff` (a single allowed prime, so `I` is a prime power), and
`Ideal.IsPrimeTo.exists_eq_pow_mul` splits off one allowed prime at a time. The file also records
the prime-power factorization `Ideal.exists_eq_prod_pow` of an arbitrary nonzero ideal. Together
with the uniqueness statement `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul` and the relative primality
`Ideal.IsPrimeTo.isRelPrime` of ideals supported on complementary sets, these are what turn a
finite set of primes into a finite Euler product in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic.lean`.

It also collects how an isomorphism `e : R ≃+* R'` moves ideals: `Ideal.map e` preserves
divisibility (`Ideal.map_dvd_map_iff_of_ringEquiv`, `Ideal.map_pow_dvd_map_iff_of_ringEquiv`,
stated over commutative *semirings*, since the proofs use only that `Ideal.map e` and
`Ideal.map e.symm` are mutually inverse) and factorisation multiplicities
(`Ideal.count_factors_map_of_ringEquiv`), and Mathlib's transport `equivOfRingEquiv e` of height
one primes is `Ideal.map e` on underlying ideals
(`IsDedekindDomain.HeightOneSpectrum.asIdeal_equivOfRingEquiv`). Those four are the ideal-level
input to the adic-valuation transport in
`TauCeti/RingTheory/DedekindDomain/AdicValuation/Transport.lean`; they are adapted from
[AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0), commit `513e83879e2f`,
`projects/HasseWeil/HasseWeil/WeilPairing/DivisorGalois.lean`.

`Ideal.IsPrimeTo` generalizes the `IsGood` predicate of
`TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, where it is stated for the bad primes
of an ideal weight on a number field; the design of the predicate — nonzeroness included, so that
`⊥` is prime to no set at all — is taken from there, while nothing in it is specific to a number
field.

The file also identifies any height-one prime of a discrete valuation ring with its maximal ideal
(`IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal`), which is what lets a condition stated at
the height-one primes of such a ring be read as a condition on its valuation. It was split out of
material adapted from Michael Stoll's elliptic-curves formalisation
(`EllipticCurves/Mathlib/AdicCompletionExtension.lean` at the roadmap's pin `66889eada51a`,
Apache 2.0, by Michael Stoll), where it is the step behind `valuation_adicCompletion_algebraMap`.

The theorem `IsDedekindDomain.HeightOneSpectrum.exists_mem_notMem` was split out of material
adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.

`IsDedekindDomain.HeightOneSpectrum.comapOfNeBot` and its projection are likewise adapted from that
formalisation (`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean`
line 539, at the roadmap's pin `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, Apache 2.0, by Michael
Stoll). The construction is the source's; what changed is the hypothesis — the source and this
version take the nonvanishing of the contraction as a hypothesis, where Mathlib's
`HeightOneSpectrum.comap` instead derives it from surjectivity of the map.

`Ideal.ne_bot_of_comap_ne_bot` plays the role of the source's
`comap_ne_bot_of_comap_comap_ne_bot` (`EllipticCurves/Mathlib/Basic.lean` line 270): it is what
discharges that nonvanishing hypothesis when a prime is contracted through an intermediate ring.
It is stated here in the general form — an arbitrary ideal and an injective ring homomorphism,
with the map producing the ideal dropped, since it plays no role — and proved from Mathlib's
`Ideal.comap_bot_of_injective`.
-/

 section

namespace Ideal

section CommSemiring

variable {R R' : Type*} [CommSemiring R] [CommSemiring R']





end CommSemiring

section RingEquivDedekind

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']



end RingEquivDedekind

section Multiplicity

variable {B : Type*} [CommRing B] [IsDedekindDomain B]



end Multiplicity

section Injective



end Injective

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

section Comap

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]





end Comap

section RingEquivTransport

variable {R R' : Type*} [CommRing R] [CommRing R']



end RingEquivTransport

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

-- `_root_` disambiguates: inside `namespace Ideal`, a bare `open IsDedekindDomain` would resolve
-- to the `Ideal.IsDedekindDomain` namespace of Mathlib's ramification indices, which the
-- `Factorization` import above makes visible here.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



variable {I J : Ideal R} {S T : Set (HeightOneSpectrum R)}

























/-- Powers of an ideal prime to `S` are again prime to `S`. -/
theorem IsPrimeTo.pow (h : IsPrimeTo I S) (n : ℕ) : IsPrimeTo (I ^ n) S := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact isPrimeTo_mul_iff.mpr ⟨ih, h⟩

/-- A nonzero power of an ideal is prime to `S` exactly when the ideal is. -/
@[simp]
theorem isPrimeTo_pow_iff {n : ℕ} (hn : n ≠ 0) : IsPrimeTo (I ^ n) S ↔ IsPrimeTo I S := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pow n⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ] at h
  exact (isPrimeTo_mul_iff.mp h).2

















end Ideal

section DiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum



end IsDedekindDomain.HeightOneSpectrum

end DiscreteValuationRing

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

/-- Restricting away from a set of primes preserves absolute convergence of the ideal-indexed
Dirichlet series, since it only replaces some terms by `0`. -/
theorem TauCeti.EulerProductData.summable_idealTerm_restrictAway (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hs : _root_.Summable (_root_.TauCeti.idealTerm K D.toIdealArithmeticFunction s)) :
    _root_.Summable (_root_.TauCeti.idealTerm K (D.restrictAway S).toIdealArithmeticFunction s) := by
  classical
  refine hs.norm.of_norm_bounded fun I ↦ ?_
  rw [_root_.TauCeti.norm_idealTerm, _root_.TauCeti.norm_idealTerm]
  gcongr
  simp only [_root_.TauCeti.EulerProductData.restrictAway_apply]
  split_ifs <;> simp

/-- Restricting away from `S` replaces the local Euler factor at a prime of `S` by `1`. -/
@[simp]
theorem TauCeti.EulerProductData.eulerFactor_restrictAway_of_mem {S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)} (hP : P ∈ S) (s : ℂ) :
    (D.restrictAway S).eulerFactor P s = 1 := by
  classical
  rw [_root_.TauCeti.EulerProductData.eulerFactor_eq_tsum, _root_.tsum_eq_single 0 fun e he ↦ ?_]
  · have h0 : P.primeIdealPow 0 = 1 := _root_.Subtype.ext (by simp)
    simp [_root_.TauCeti.idealTerm_def, h0, _root_.Ideal.one_eq_top, _root_.Ideal.isPrimeTo_top, D.isMultiplicative.map_one]
  · have hnot : ¬ _root_.Ideal.IsPrimeTo (P.asIdeal ^ e) S := by
      rw [_root_.Ideal.isPrimeTo_pow_iff he, _root_.Ideal.isPrimeTo_asIdeal_iff]
      exact _root_.not_not_intro hP
    simp [_root_.TauCeti.idealTerm_def, hnot]

/-- Restricting away from `S` leaves the local Euler factor at a prime outside `S` unchanged. -/
@[simp]
theorem TauCeti.EulerProductData.eulerFactor_restrictAway_of_notMem {S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)} (hP : P ∉ S) (s : ℂ) :
    (D.restrictAway S).eulerFactor P s = D.eulerFactor P s := by
  classical
  rw [_root_.TauCeti.EulerProductData.eulerFactor_eq_tsum, _root_.TauCeti.EulerProductData.eulerFactor_eq_tsum]
  refine _root_.tsum_congr fun e ↦ ?_
  have hprime : _root_.Ideal.IsPrimeTo (P.asIdeal ^ e) S := (Ideal.isPrimeTo_asIdeal_iff.mpr hP).pow e
  simp [_root_.TauCeti.idealTerm_def, hprime]

/-- **Deleting finitely many Euler factors.** Where the ideal-indexed Dirichlet series of `D`
converges absolutely, restricting `D` away from a finite set `S` of primes divides its `L`-series
by the local Euler factors at `S`: multiplying them back recovers the `L`-series of `D`. -/
theorem solution (S : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hs : _root_.Summable (_root_.TauCeti.idealTerm K D.toIdealArithmeticFunction s)) :
    _root_.LSeries (_root_.TauCeti.normCoeff K (D.restrictAway S).toIdealArithmeticFunction) s *
        ∏ P ∈ S, D.eulerFactor P s =
      _root_.LSeries (_root_.TauCeti.normCoeff K D.toIdealArithmeticFunction) s := by
  classical
  -- The Euler factors of the restriction are those of `D` off `S` and `1` on `S`, so multiplying
  -- them by the finitely many factors of `D` at `S` recovers the Euler product of `D`.
  have hS : _root_.HasProd (fun P ↦ if P ∈ S then D.eulerFactor P s else 1)
      (∏ P ∈ S, D.eulerFactor P s) := by
    have h := _root_.hasProd_prod_of_ne_finset_one (s := S) (L := _root_.SummationFilter.unconditional _)
      (f := fun P ↦ if P ∈ S then D.eulerFactor P s else 1) fun P hP ↦ by simp [hP]
    rwa [_root_.Finset.prod_ite_mem, _root_.Finset.inter_self] at h
  have hfun : ∀ P, D.eulerFactor P s =
      (D.restrictAway S).eulerFactor P s * if P ∈ S then D.eulerFactor P s else 1 := fun P ↦ by
    by_cases hP : P ∈ S
    · simp [hP, D.eulerFactor_restrictAway_of_mem (Finset.mem_coe.mpr hP)]
    · simp [hP, D.eulerFactor_restrictAway_of_notMem (_root_.mt Finset.mem_coe.mp hP)]
  exact ((D.hasProd_eulerFactor hs).unique (((D.restrictAway S).hasProd_eulerFactor
    (D.summable_idealTerm_restrictAway S hs)).mul hS |>.congr_fun hfun)).symm

end EulerProductData

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K) {s : ℂ}



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
