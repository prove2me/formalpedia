-- Prove2me | solution 1 for TauCeti.NumberFieldArithmetic.idealsAway_eq_closure_primes
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:22:42.534854+00:00
-- url     : https://prove2.me/submissions/4493a31b-c476-46b1-b01a-342c9a7b7e26

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Theorems.Thm_FractionalIdeal_finprod_unitOfPrime_zpow_count

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complements on Dedekind-domain factorization

Facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry, together
with unit-level factorization of invertible fractional ideals.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.le_count_associates_iff_le_pow`: the multiplicity of `v` in
  a nonzero `J` is at least `k` exactly when `v ^ k` contains `J`. The multiplicity here is
  `Associates.count`, not `FractionalIdeal.count` — hence the `associates` token, matching
  Mathlib's `Ideal.count_associates_factors_eq` for the same expression. Mathlib reads that
  multiplicity as divisibility of `Associates`; a consumer comparing two multiplicities across a
  ring extension wants a containment of *ideals*, and shows the two ideals contain the same prime
  powers.
* `FractionalIdeal.count_div`: the multiplicity of `I / J` is the difference of the multiplicities
  of `I` and `J`. Mathlib's `count` API has `count_mul`, `count_inv`, `count_pow` and `count_zpow`
  but no division form, so every consumer that clears a denominator repeats the same rewrites.
* `FractionalIdeal.count_spanSingleton_div`: the same on principal fractional ideals. This is the
  one the `S`-integer class-group computation in
  `TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean` uses, at both `R` and `𝒪_S` — which
  is why the ring is a variable rather than fixed — advancing
  `TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 (Mordell–Weil), whose weak-Mordell–Weil
  argument needs the `S`-class group to be finite. It is also the step that carries
  `count_toPrincipalIdeal_eq_neg_log_valuation` below. `count_div` is its general form and has no
  consumer in this repository yet.
* `FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`: the multiplicity at `v` of the
  principal fractional ideal of a nonzero rational function `u : Kˣ` is
  `-WithZero.log (v.valuation K u)`. This is the passage between the two ways this library measures
  a principal ideal at a height one prime — Mathlib's `count` and the adic valuation.
* `Ideal.hasFiniteMulSupport_asIdeal_pow_of_le_count`: a family of prime powers whose exponents
  are bounded by the multiplicities of a fixed nonzero ideal has finite multiplicative support.
  Mathlib's `Ideal.hasFiniteMulSupport` is the case of the multiplicities themselves; a consumer
  defining an ideal as `∏ᵥ 𝔭ᵥ ^ e v` for exponents it only knows to be dominated by an actual
  factorisation — as the minimal discriminant ideal of an elliptic curve is dominated by the
  discriminant of any integral model — needs the bounded form to see that the product is finite.
* `IsDedekindDomain.HeightOneSpectrum.unitOfPrime`: a height-one prime regarded as an invertible
  fractional ideal.
* `FractionalIdeal.hasFiniteMulSupport_zpow_count`: a family of powers indexed by the height one
  primes, with the multiplicities of a fixed fractional ideal as exponents, has finite
  multiplicative support. The bases are an arbitrary family in an arbitrary `DivInvMonoid`, since
  nothing but the vanishing of almost all exponents is at stake; the unit-level factorization below
  is the case of the primes themselves.
* `FractionalIdeal.finprod_unitOfPrime_zpow_count`: unique factorization of an invertible
  fractional ideal, transported along `Units.coeHom`.

All these declarations are general facts about an arbitrary Dedekind domain, mentioning no
particular ring extension.

`le_count_associates_iff_le_pow` is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.
**`count_div` and `count_spanSingleton_div` are new here** — they have no counterpart in that
source. `count_toPrincipalIdeal_eq_neg_log_valuation` is this repository's own, relocated here
from `TauCeti/AlgebraicGeometry/WeilDivisor/Dedekind/Basic.lean`: nothing in its statement or
proof mentions a Weil divisor, and stating it under `TauCeti.AlgebraicGeometry` put it out of
reach of the `RingTheory` consumers that need it, which is exactly the boundary
`TauCeti/RingTheory/ClassGroup/HeightOneSpectrum.lean` records in its module docstring.

The unit-level prime factorization `FractionalIdeal.finprod_unitOfPrime_zpow_count` is adapted
from Michael Stoll's `EllipticCurves/Mathlib/FractionalIdeal.lean` at commit `66889eada51a` of the
`MichaelStollBayreuth/EllipticCurves` repository (Apache 2.0).
-/
 section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



/-- The fractional ideal underlying `v.unitOfPrime K` is `v.asIdeal`. -/
@[simp]
theorem coe_unitOfPrime (v : HeightOneSpectrum R) (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] :
    (v.unitOfPrime K : FractionalIdeal R⁰ K) = v.asIdeal := by
  rw [unitOfPrime]
  exact Units.val_mk0 _



end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

-- `Ideal.IsDedekindDomain` also exists, so the root namespace has to be named explicitly.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



end Ideal

namespace FractionalIdeal

open IsDedekindDomain

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]



/-- Only finitely many factors in the unit-level prime factorization are nontrivial. -/
lemma hasFiniteMulSupport_unitOfPrime_zpow (I : (FractionalIdeal R⁰ K)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum R ↦
      v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K)).Finite :=
  hasFiniteMulSupport_zpow_count (I : FractionalIdeal R⁰ K) (fun v ↦ v.unitOfPrime K)







section PrincipalIdeal

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]





end PrincipalIdeal

end FractionalIdeal

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
# Fractional ideals away from finitely many primes

For a number field `K` and a finite set `S` of its finite places, this file defines the subgroup
`idealsAway S` of invertible fractional ideals whose multiplicity vanishes at every member of
`S`. It proves that this subgroup is generated by the prime ideals outside `S` and supplies the
inclusion induced by enlarging `S`.

The integral counterpart `integralIdealsAway S` consists of the nonzero integral ideals divisible
by no prime in `S`. Its map to `idealsAway S` is the restriction of Mathlib's
`FractionalIdeal.mk0`.

The generation proof transports Mathlib's unique factorization of a nonzero fractional ideal,
`FractionalIdeal.finprod_heightOneSpectrum_factorization'`, to fractional-ideal units.

## Main definitions

* `NumberFieldArithmetic.idealsAway`: unit fractional ideals trivial at the primes in `S`.
* `NumberFieldArithmetic.idealsAwayEmptyEquiv`: ideals away from no primes are all invertible
  fractional ideals.
* `NumberFieldArithmetic.idealsAwayInclusion`: inclusion obtained from `S ⊆ S'`.
* `NumberFieldArithmetic.integralIdealsAway`: nonzero integral ideals prime to `S`.
* `NumberFieldArithmetic.integralIdealsAwayHom`: the map from integral to fractional ideals.

## Main results

* `NumberFieldArithmetic.integralIdealsAway_hom_ext`: a monoid homomorphism out of
  `integralIdealsAway S` is determined by its values on the primes outside `S`.

## References

The shared lift of fractional-ideal factorization to units,
`FractionalIdeal.finprod_unitOfPrime_zpow_count`, is also used by
`TauCeti.RingTheory.ClassGroup.HeightOneSpectrum`. It is adapted from Michael Stoll's
`EllipticCurves/Mathlib/FractionalIdeal.lean` at commit `66889eada51a` of the
`MichaelStollBayreuth/EllipticCurves` repository (Apache 2.0).
-/

 section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.NumberFieldArithmetic
end TauCeti.NumberFieldArithmetic
section TauCeti.NumberFieldArithmetic
open TauCeti TauCeti.NumberFieldArithmetic

variable {K : Type*} [Field K] [NumberField K]

















/-- `idealsAway S` is generated by the height-one prime ideals outside `S`. -/
theorem solution (S : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    _root_.TauCeti.NumberFieldArithmetic.idealsAway S = _root_.Subgroup.closure {I : (_root_.FractionalIdeal (𝓞 K)⁰ K)ˣ |
      ∃ v : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∉ S ∧
        ((I : _root_.FractionalIdeal (𝓞 K)⁰ K) =
          (v.asIdeal : _root_.FractionalIdeal (𝓞 K)⁰ K))} := by
  apply _root_.le_antisymm
  · intro I hI
    classical
    have hfin := _root_.FractionalIdeal.hasFiniteMulSupport_unitOfPrime_zpow (K := K) I
    rw [_root_.FractionalIdeal.finprod_unitOfPrime_zpow_count I,
      _root_.finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin (_root_.Finset.Subset.refl _)]
    refine _root_.Subgroup.prod_mem _ fun v hv ↦ _root_.Subgroup.zpow_mem _ (_root_.Subgroup.subset_closure ?_) _
    refine ⟨v, ?_, v.coe_unitOfPrime K⟩
    intro hvS
    exact (hfin.mem_toFinset.mp hv) (by simp only [hI v hvS, _root_.zpow_zero])
  · refine (_root_.Subgroup.closure_le _).mpr ?_
    rintro I ⟨v, hv, hI⟩ w hw
    have hwv : w ≠ v := fun hwv ↦ hv (hwv ▸ hw)
    rw [hI, _root_.FractionalIdeal.count_maximal_coprime K w hwv.symm]

















end TauCeti.NumberFieldArithmetic

end
end
