-- Prove2me | solution 1 for TauCeti.IdealArithmeticFunction.normCoeff_supportedPart_singleton
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:06.061032+00:00
-- url     : https://prove2.me/submissions/e9d38274-e5e0-4123-8255-2d5cf0a4a09b

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring

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







/-- An ideal divisible by no height-one prime other than `𝔭` is a power of `𝔭`. -/
theorem isPrimeTo_compl_singleton_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo I {𝔭}ᶜ ↔ ∃ n : ℕ, I = 𝔭.asIdeal ^ n := by
  constructor
  · intro h
    refine h.induction_on ⟨0, by simp⟩ ?_
    rintro 𝔮 J h𝔮 - ⟨n, rfl⟩
    rw [Set.notMem_compl_iff, Set.mem_singleton_iff] at h𝔮
    exact ⟨n + 1, by rw [h𝔮, pow_succ']⟩
  · rintro ⟨n, rfl⟩
    exact (isPrimeTo_asIdeal_iff.mpr (by simp)).pow n











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
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API exposes the finite norm fibre
`TauCeti.normFiber` and its finiteness, records the value at one, proves compatibility with
complex conjugation, and records in `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg` that no
cancellation occurs inside a fibre when the values of `f` are nonnegative.  Regrouping is
compatible with transporting along an isomorphism of number fields: `TauCeti.normCoeff_map` says
that an isomorphism `e : K ≃+* L` leaves every norm coefficient unchanged.

Regrouping loses information as soon as a norm fibre has more than one element:
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` produces a nonzero ideal arithmetic
function, with a negative value, whose norm coefficients all vanish.  This is the rejection test
that forbids weakening the nonnegativity hypothesis of the converse regrouping theorem to
nonnegativity of the coefficients themselves.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next layer step uses these coefficients
to regroup an absolutely convergent series over nonzero ideals into a Mathlib `LSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]















/-- The value of `normCoeff f` is the finite sum of `f` over the corresponding absolute-norm
fibre. -/
theorem normCoeff_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I :=
  (rfl)

/-- The value of `normCoeff f` as a sum over the finite absolute-norm fibre. -/
theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [normFiber]















/-! ### The cancellation rejection test -/



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
end IsDedekindDomain.HeightOneSpectrum
section IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K]



/-- A prime power, as a nonzero integral ideal, has the expected underlying ideal. -/
@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.coe_primeIdealPow (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (_root_.IsDedekindDomain.HeightOneSpectrum.primeIdealPow P e : _root_.Ideal (𝓞 K)) = P.asIdeal ^ e :=
  (_root_.rfl)

variable [NumberField K]







end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti



namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]



omit [_root_.NumberField K] in
/-- Coefficients of the canonical local power series are the prime-power values of `f`. -/
@[simp]
theorem TauCeti.IdealArithmeticFunction.coeff_localPowerSeries (f : _root_.TauCeti.IdealArithmeticFunction K)
    (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    _root_.PowerSeries.coeff n (_root_.TauCeti.IdealArithmeticFunction.localPowerSeries f P) =
      f (P.primeIdealPow n) := by
  simp only [_root_.TauCeti.IdealArithmeticFunction.localPowerSeries, _root_.PowerSeries.coeff_mk]
  exact _root_.congrArg f (_root_.Subtype.ext (P.coe_primeIdealPow n).symm)







/-- At a power of `N(P)`, the local arithmetic factor is the corresponding value at `P ^ n`. -/
@[simp]
theorem TauCeti.IdealArithmeticFunction.localArithmeticFactor_apply_pow (f : _root_.TauCeti.IdealArithmeticFunction K)
    (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    _root_.TauCeti.IdealArithmeticFunction.localArithmeticFactor f P (_root_.Ideal.absNorm P.asIdeal ^ n) =
      f (P.primeIdealPow n) := by
  rw [_root_.TauCeti.IdealArithmeticFunction.localArithmeticFactor, _root_.ArithmeticFunction.ofPowerSeries_apply_pow
    (_root_.NumberField.HeightOneSpectrum.one_lt_absNorm P)]
  exact _root_.TauCeti.IdealArithmeticFunction.coeff_localPowerSeries f P n

/-- A local arithmetic factor vanishes away from powers of its prime-ideal norm. -/
@[simp]
theorem TauCeti.IdealArithmeticFunction.localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq (f : _root_.TauCeti.IdealArithmeticFunction K)
    (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ ∃ n : ℕ, _root_.Ideal.absNorm P.asIdeal ^ n = m) :
    _root_.TauCeti.IdealArithmeticFunction.localArithmeticFactor f P m = 0 := by
  rw [_root_.TauCeti.IdealArithmeticFunction.localArithmeticFactor, _root_.ArithmeticFunction.ofPowerSeries_apply
    (_root_.NumberField.HeightOneSpectrum.one_lt_absNorm P),
    _root_.Function.extend_apply' _ _ _ (by simpa using hm), _root_.Pi.zero_apply]













/-! ### Finite Euler products -/



variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}





omit [_root_.NumberField K] in
/-- The restriction of `f` to `S` is supported on the ideals supported on `S`. -/
theorem TauCeti.IdealArithmeticFunction.isPrimeTo_compl_of_supportedPart_apply_ne_zero (hA : _root_.TauCeti.IdealArithmeticFunction.supportedPart f S A ≠ 0) :
    _root_.Ideal.IsPrimeTo (A : _root_.Ideal (𝓞 K)) Sᶜ :=
  not_not.mp fun h ↦ hA (_root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl h)









/-- **A surviving `{P}`-part is a power of `P`.**  The restriction to the powers of a single prime
kills every ideal not prime to `{P}ᶜ`, and for a single prime that condition is exactly being a
power of `P`. -/
private theorem TauCeti.IdealArithmeticFunction.exists_eq_pow_of_supportedPart_singleton_apply_ne_zero
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {I : (_root_.Ideal (𝓞 K))⁰} (hI : _root_.TauCeti.IdealArithmeticFunction.supportedPart f {P} I ≠ 0) :
    ∃ m : ℕ, (I : _root_.Ideal (𝓞 K)) = P.asIdeal ^ m :=
  Ideal.isPrimeTo_compl_singleton_iff.mp (_root_.TauCeti.IdealArithmeticFunction.isPrimeTo_compl_of_supportedPart_apply_ne_zero hI)







/-- The norm coefficients of the restriction to the powers of a single prime `P` are exactly its
canonical local arithmetic factor. -/

theorem solution (f : _root_.TauCeti.IdealArithmeticFunction K)
    (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    _root_.TauCeti.normCoeff K (_root_.TauCeti.IdealArithmeticFunction.supportedPart f {P}) = _root_.TauCeti.IdealArithmeticFunction.localArithmeticFactor f P := by
  have h2 : 2 ≤ _root_.Ideal.absNorm P.asIdeal := _root_.NumberField.HeightOneSpectrum.one_lt_absNorm P
  ext n
  rw [_root_.TauCeti.normCoeff_eq_sum_normFiber]
  by_cases hn : ∃ k : ℕ, _root_.Ideal.absNorm P.asIdeal ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    obtain ⟨C, hCval⟩ : ∃ C : (_root_.Ideal (𝓞 K))⁰, (C : _root_.Ideal (𝓞 K)) = P.asIdeal ^ k :=
      ⟨⟨_, _root_.mem_nonZeroDivisors_of_ne_zero (_root_.pow_ne_zero k P.ne_bot)⟩, _root_.rfl⟩
    have hCmem : C ∈ _root_.TauCeti.normFiber K (_root_.Ideal.absNorm P.asIdeal ^ k) := by
      rw [_root_.TauCeti.mem_normFiber, hCval, _root_.map_pow]
    have hother : ∀ I ∈ _root_.TauCeti.normFiber K (_root_.Ideal.absNorm P.asIdeal ^ k), I ≠ C →
        _root_.TauCeti.IdealArithmeticFunction.supportedPart f ({P} : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))) I = 0 := by
      intro I hI hIC
      by_contra hI0
      obtain ⟨j, hj⟩ := _root_.TauCeti.IdealArithmeticFunction.exists_eq_pow_of_supportedPart_singleton_apply_ne_zero hI0
      have hjk : _root_.Ideal.absNorm P.asIdeal ^ j = _root_.Ideal.absNorm P.asIdeal ^ k := by
        rw [← _root_.map_pow, ← hj]
        exact (_root_.TauCeti.mem_normFiber K).mp hI
      exact hIC (_root_.Subtype.ext (by rw [hj, hCval, _root_.Nat.pow_right_injective h2 hjk]))
    rw [_root_.Finset.sum_eq_single_of_mem C hCmem hother, _root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl
      (by rw [hCval]; exact Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨k, _root_.rfl⟩),
      _root_.TauCeti.IdealArithmeticFunction.localArithmeticFactor_apply_pow]
    exact _root_.congrArg f (_root_.Subtype.ext hCval)
  · rw [_root_.TauCeti.IdealArithmeticFunction.localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq f P hn]
    refine _root_.Finset.sum_eq_zero fun I hI ↦ ?_
    by_contra hI0
    obtain ⟨j, hj⟩ := _root_.TauCeti.IdealArithmeticFunction.exists_eq_pow_of_supportedPart_singleton_apply_ne_zero hI0
    exact hn ⟨j, by rw [← _root_.map_pow, ← hj]; exact (_root_.TauCeti.mem_normFiber K).mp hI⟩







end IdealArithmeticFunction

end TauCeti

end
end
