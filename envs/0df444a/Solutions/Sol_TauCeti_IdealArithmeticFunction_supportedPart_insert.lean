-- Prove2me | solution 1 for TauCeti.IdealArithmeticFunction.supportedPart_insert
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:07.767356+00:00
-- url     : https://prove2.me/submissions/ec49288e-47c8-499c-889b-65d7b3989596

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Convolution
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
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













omit [IsDedekindDomain R] in
theorem IsPrimeTo.mono (hST : S ⊆ T) (h : IsPrimeTo I T) : IsPrimeTo I S :=
  ⟨h.ne_bot, fun _𝔭 h𝔭 ↦ h.not_dvd (hST h𝔭)⟩











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

/-- **Ideals supported on complementary sets of primes are relatively prime.** -/
theorem IsPrimeTo.isRelPrime (hI : IsPrimeTo I S) (hJ : IsPrimeTo J Sᶜ) : IsRelPrime I J := by
  refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors
    (by simpa using hI.ne_bot)).mpr fun d hdI hdJ hd ↦ ?_
  have h𝔭 : HeightOneSpectrum.ofPrime hd ∉ Sᶜ := fun h ↦ hJ.not_dvd h hdJ
  exact hI.not_dvd (Set.notMem_compl_iff.mp h𝔭) hdI



/-- **Splitting off one allowed prime.** An ideal all of whose prime factors lie in `insert 𝔭 S`
is a power of `𝔭` times an ideal all of whose prime factors lie in `S`. -/
theorem IsPrimeTo.exists_eq_pow_mul {𝔭 : HeightOneSpectrum R} (h : IsPrimeTo I (insert 𝔭 S)ᶜ) :
    ∃ (n : ℕ) (J : Ideal R), IsPrimeTo J Sᶜ ∧ I = 𝔭.asIdeal ^ n * J := by
  have hmax := 𝔭.isMaximal
  obtain ⟨Q, hQsup, heq⟩ := Ideal.eq_prime_pow_mul_coprime h.ne_bot 𝔭.asIdeal
  refine ⟨_, Q, ⟨fun hQ ↦ h.ne_bot (by rw [heq, hQ, Ideal.mul_bot]), fun 𝔮 h𝔮 hdvd ↦ ?_⟩, heq⟩
  -- A prime dividing the cofactor divides the whole ideal, so it is excluded unless it is `𝔭`;
  -- and `𝔭` cannot divide the cofactor, which Mathlib returns coprime to `𝔭`.
  refine h.not_dvd ?_ (by rw [heq]; exact hdvd.mul_left _)
  rw [Set.mem_compl_iff, Set.mem_insert_iff]
  rintro (rfl | h𝔮')
  · exact hmax.ne_top (by rwa [sup_eq_left.mpr (Ideal.le_of_dvd hdvd)] at hQsup)
  · exact h𝔮 h𝔮'

private theorem multiplicity_pow_mul {p J : Ideal R} (hp : p ≠ ⊥) (hJ : ¬ p ∣ J) (n : ℕ) :
    multiplicity p (p ^ n * J) = n := by
  refine multiplicity_eq_of_dvd_of_not_dvd (Dvd.intro _ rfl) fun hdvd ↦ hJ ?_
  rw [pow_succ] at hdvd
  exact (mul_dvd_mul_iff_left (pow_ne_zero n (by simpa using hp))).mp hdvd

/-- **Uniqueness of the splitting.** The exponent and the prime-to-`p` cofactor of a nonzero
ideal are determined by it. Only nonzeroness of `p` is used, not primality. -/
theorem eq_and_eq_of_pow_mul_eq_pow_mul {p : Ideal R} (hp : p ≠ ⊥) {m n : ℕ} {I J : Ideal R}
    (hI : ¬ p ∣ I) (hJ : ¬ p ∣ J) (h : p ^ m * I = p ^ n * J) : m = n ∧ I = J := by
  have hmn : m = n := by
    have hm := multiplicity_pow_mul hp hI m
    rw [h, multiplicity_pow_mul hp hJ n] at hm
    exact hm.symm
  refine ⟨hmn, ?_⟩
  subst hmn
  exact mul_left_cancel₀ (pow_ne_zero _ (by simpa using hp)) h

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
# Ideal convolution of ideal arithmetic functions

The Dirichlet convolution of two arithmetic functions on the nonzero ideals of the ring of integers
of a number field `K` sums over the factorizations `B * C = A` of a nonzero ideal `A`. This file
constructs that index set, defines the convolution, and proves that it makes
`TauCeti.IdealArithmeticFunction K` a commutative monoid with identity
`TauCeti.IdealArithmeticFunction.delta`, bilinear over the pointwise additive structure.
It also transports this operation through `TauCeti.normCoeff` to Mathlib's Dirichlet convolution
on `ArithmeticFunction ℂ`.

## Main definitions

* `TauCeti.IdealArithmeticFunction.delta` is the ideal arithmetic function that is `1` at the unit
  ideal and `0` elsewhere.
* `TauCeti.Ideal.divisorsAntidiagonal A` is the finite set of pairs `(B, C)` of nonzero ideals with
  `B * C = A`; it is the ideal analogue of Mathlib's `Nat.divisorsAntidiagonal`.
* `TauCeti.IdealArithmeticFunction.convolution f g` is the ideal Dirichlet convolution.
* `TauCeti.IdealArithmeticFunction.convolutionPow f n` is the `n`-fold convolution power of `f`.

## Main results

* `TauCeti.IdealArithmeticFunction.convolution_comm`,
  `TauCeti.IdealArithmeticFunction.convolution_assoc`,
  `TauCeti.IdealArithmeticFunction.delta_convolution` and
  `TauCeti.IdealArithmeticFunction.convolution_delta`: the convolution monoid laws.
* `TauCeti.IdealArithmeticFunction.convolution_add` and
  `TauCeti.IdealArithmeticFunction.add_convolution`: bilinearity over pointwise addition.
* `TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul`: ideal convolution is not the
  pointwise product.
* `TauCeti.normCoeff_delta`, `TauCeti.normCoeff_convolution`, and
  `TauCeti.normCoeff_convolutionPow`: regrouping by absolute norm transports the convolution
  identity, convolution, and convolution powers to Mathlib arithmetic functions.

## Implementation notes

`TauCeti.IdealArithmeticFunction K` is a `Pi` type, so it already carries Mathlib's *pointwise*
`CommRing` structure, in which `f * g` is `fun A => f A * g A` and `1` is the everywhere-one
function. Convolution is therefore deliberately **not** registered as a `Mul` instance and its
identity is the separate function `TauCeti.IdealArithmeticFunction.delta`; this is the roadmap's
convention that pointwise multiplication and ideal convolution stay distinct operations on one
carrier. The monoid laws are stated as ordinary theorems about
`TauCeti.IdealArithmeticFunction.convolution`, and
`TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul` records that the two products really do
differ. Consequently iterated convolution is the explicit
`TauCeti.IdealArithmeticFunction.convolutionPow` rather than a `Monoid.npow`.

Excluding the zero ideal from the carrier is what makes the index set finite: `⊥ * J = ⊥` for every
`J`, so the zero ideal has infinitely many factorizations while a nonzero ideal has only finitely
many, by Mathlib's `UniqueFactorizationMonoid.fintypeSubtypeDvd` for the unique factorization
monoid `Ideal (𝓞 K)`.

## Roadmap role

This is Layer **2.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, built on the Layer
**0.1** carrier of `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`. Its consumers are
the ideal Möbius function and von Mangoldt transform of Layer 2 and the local factors of Layer 3.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped nonZeroDivisors NumberField

namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

/-! ### The convolution identity -/









end IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

namespace Ideal

/-! ### The antidiagonal of a nonzero ideal -/





/-- A pair lies in the antidiagonal of `A` exactly when its two entries multiply to `A`. -/
@[simp]
theorem mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰} {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} :
    p ∈ divisorsAntidiagonal A ↔ p.1 * p.2 = A := by
  simp [divisorsAntidiagonal]











end Ideal

namespace IdealArithmeticFunction

/-! ### Ideal convolution -/



/-- The defining formula for ideal convolution. -/
@[simp]
theorem convolution_apply (f g : IdealArithmeticFunction K) (A : (Ideal (𝓞 K))⁰) :
    convolution f g A = ∑ p ∈ Ideal.divisorsAntidiagonal A, f p.1 * g p.2 :=
  (rfl)



/-! ### The monoid laws -/









/-! ### Bilinearity over the pointwise additive structure -/





















/-! ### Iterated convolution -/













/-! ### Convolution is not the pointwise product -/





end IdealArithmeticFunction

/-! ## Compatibility with Dirichlet convolution -/

variable (K : Type*) [Field K] [NumberField K]







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

/-- **Only the `S`-part/`P`-part pair survives.**  Where `A` is `P ^ n` times an ideal `B` prime to
`Sᶜ`, and `C` is that power of `P`, every pair of the antidiagonal of `A` other than `(B, C)`
contributes zero to the convolution. -/
private theorem TauCeti.IdealArithmeticFunction.supportedPart_mul_eq_zero_of_ne {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)} (hPS : P ∈ Sᶜ)
    {A B C : (_root_.Ideal (𝓞 K))⁰} {n : ℕ} (hB : _root_.Ideal.IsPrimeTo (B : _root_.Ideal (𝓞 K)) Sᶜ)
    (hC : (C : _root_.Ideal (𝓞 K)) = P.asIdeal ^ n)
    (hA : (A : _root_.Ideal (𝓞 K)) = P.asIdeal ^ n * (B : _root_.Ideal (𝓞 K))) :
    ∀ p ∈ _root_.TauCeti.Ideal.divisorsAntidiagonal A, p ≠ (B, C) →
      _root_.TauCeti.IdealArithmeticFunction.supportedPart f S p.1 * _root_.TauCeti.IdealArithmeticFunction.supportedPart f {P} p.2 = 0 := by
  intro p hp hne
  by_contra hp0
  have h1 := _root_.TauCeti.IdealArithmeticFunction.isPrimeTo_compl_of_supportedPart_apply_ne_zero (_root_.left_ne_zero_of_mul hp0)
  obtain ⟨m, h2⟩ :=
    _root_.TauCeti.IdealArithmeticFunction.exists_eq_pow_of_supportedPart_singleton_apply_ne_zero (_root_.right_ne_zero_of_mul hp0)
  have hmul : (p.1 : _root_.Ideal (𝓞 K)) * (p.2 : _root_.Ideal (𝓞 K)) = (A : _root_.Ideal (𝓞 K)) := by
    rw [← _root_.Submonoid.coe_mul, Ideal.mem_divisorsAntidiagonal.mp hp]
  have heq : P.asIdeal ^ m * (p.1 : _root_.Ideal (𝓞 K)) = P.asIdeal ^ n * (B : _root_.Ideal (𝓞 K)) := by
    rw [← h2, _root_.mul_comm, hmul, hA]
  obtain ⟨rfl, hval⟩ :=
    _root_.Ideal.eq_and_eq_of_pow_mul_eq_pow_mul P.ne_bot (h1.not_dvd hPS) (hB.not_dvd hPS) heq
  exact hne (_root_.Prod.ext (_root_.Subtype.ext hval) (_root_.Subtype.ext (h2.trans hC.symm)))

/-- **A nonvanishing summand forces the support.**  If any pair in the antidiagonal of `A`
contributes to the convolution, then `A` itself is prime to `(insert P S)ᶜ`: its left factor is
prime to `Sᶜ` and its right factor is a power of `P`. -/
private theorem TauCeti.IdealArithmeticFunction.isPrimeTo_compl_insert_of_supportedPart_mul_ne_zero
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {A : (_root_.Ideal (𝓞 K))⁰} {p : (_root_.Ideal (𝓞 K))⁰ × (_root_.Ideal (𝓞 K))⁰}
    (hp : p ∈ _root_.TauCeti.Ideal.divisorsAntidiagonal A)
    (hp0 : _root_.TauCeti.IdealArithmeticFunction.supportedPart f S p.1 * _root_.TauCeti.IdealArithmeticFunction.supportedPart f {P} p.2 ≠ 0) :
    _root_.Ideal.IsPrimeTo (A : _root_.Ideal (𝓞 K)) (_root_.Insert.insert P S)ᶜ := by
  have h1 := _root_.TauCeti.IdealArithmeticFunction.isPrimeTo_compl_of_supportedPart_apply_ne_zero (_root_.left_ne_zero_of_mul hp0)
  obtain ⟨m, h2⟩ :=
    _root_.TauCeti.IdealArithmeticFunction.exists_eq_pow_of_supportedPart_singleton_apply_ne_zero (_root_.right_ne_zero_of_mul hp0)
  rw [← _root_.congrArg _root_.Subtype.val (Ideal.mem_divisorsAntidiagonal.mp hp), _root_.Submonoid.coe_mul]
  refine Ideal.isPrimeTo_mul_iff.mpr
    ⟨h1.mono (Set.compl_subset_compl.mpr (_root_.Set.subset_insert P S)), ?_⟩
  rw [h2]
  exact (Ideal.isPrimeTo_asIdeal_iff.mpr (by simp)).pow m

/-- **Splitting off one prime.** For a multiplicative `f`, adjoining a prime `P ∉ S` to the support
convolves the restriction to `S` with the restriction to the powers of `P`; the factorization of an
ideal supported on `insert P S` into its `P`-part and its `S`-part is unique, so exactly one
summand of the convolution survives. -/
theorem solution (hf : f.IsMultiplicative) {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    (hP : P ∉ S) :
    _root_.TauCeti.IdealArithmeticFunction.supportedPart f (_root_.Insert.insert P S) = _root_.TauCeti.IdealArithmeticFunction.convolution (_root_.TauCeti.IdealArithmeticFunction.supportedPart f S) (_root_.TauCeti.IdealArithmeticFunction.supportedPart f {P}) := by
  have hPS : P ∈ Sᶜ := _root_.Set.mem_compl hP
  funext A
  rw [_root_.TauCeti.IdealArithmeticFunction.convolution_apply]
  by_cases hA : _root_.Ideal.IsPrimeTo (A : _root_.Ideal (𝓞 K)) (_root_.Insert.insert P S)ᶜ
  · obtain ⟨n, J, hJ, hAJ⟩ := hA.exists_eq_pow_mul (𝔭 := P)
    obtain ⟨B, rfl⟩ : ∃ B : (_root_.Ideal (𝓞 K))⁰, (B : _root_.Ideal (𝓞 K)) = J :=
      ⟨⟨J, _root_.mem_nonZeroDivisors_of_ne_zero (by simpa using hJ.ne_bot)⟩, _root_.rfl⟩
    have hCP : _root_.Ideal.IsPrimeTo ((P.primeIdealPow n : (_root_.Ideal (𝓞 K))⁰) : _root_.Ideal (𝓞 K))
        ({P} : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))ᶜ :=
      Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨n, P.coe_primeIdealPow n⟩
    have hBC : B * P.primeIdealPow n = A :=
      _root_.Subtype.ext (by rw [_root_.Submonoid.coe_mul, P.coe_primeIdealPow, _root_.mul_comm, ← hAJ])
    rw [_root_.Finset.sum_eq_single_of_mem (B, P.primeIdealPow n)
        (Ideal.mem_divisorsAntidiagonal.mpr hBC)
        (_root_.TauCeti.IdealArithmeticFunction.supportedPart_mul_eq_zero_of_ne hPS hJ (P.coe_primeIdealPow n) hAJ),
      _root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hA, _root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hJ,
      _root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hCP,
      ← hf.map_mul_of_isRelPrime
        ((hJ.mono (Set.singleton_subset_iff.mpr hPS)).isRelPrime hCP), hBC]
  · rw [_root_.TauCeti.IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl hA]
    exact (_root_.Finset.sum_eq_zero fun p hp ↦ not_not.mp fun hp0 ↦
      hA (_root_.TauCeti.IdealArithmeticFunction.isPrimeTo_compl_insert_of_supportedPart_mul_ne_zero hp hp0)).symm









end IdealArithmeticFunction

end TauCeti

end
end
