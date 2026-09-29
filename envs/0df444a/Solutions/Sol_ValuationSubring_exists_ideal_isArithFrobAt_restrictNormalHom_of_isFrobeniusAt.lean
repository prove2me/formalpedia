-- Prove2me | solution 1 for ValuationSubring.exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b0c16e1b-61f9-5a72-996d-9334623ad2b5

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt

set_option autoImplicit false

open scoped NumberField Pointwise

namespace FrobDictEngine

open NumberField ValuationSubring

section Place

variable {L : Type*} [Field L]

theorem natCast_mem_maximalIdeal (A : ValuationSubring L) {q : ℕ} (hA : A.LiesOverPrime q) :
    (q : A) ∈ IsLocalRing.maximalIdeal A := by
  rw [← coe_mem_nonunits_iff]
  exact hA

variable {K : Type*} [Field K] [Algebra K L]

theorem smul_sub_pow_mem_nonunits {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) {x : L} (hx : x ∈ A) : σ x - x ^ q ∈ A.nonunits := by
  set a : A := ⟨x, hx⟩ with ha
  set g : A.decompositionSubgroup K := ⟨σ, h.mem_decompositionSubgroup⟩ with hg
  have h1 : IsLocalRing.residue A (g • a) = IsLocalRing.residue A (a ^ q) := by
    rw [map_pow, IsLocalRing.ResidueField.residue_smul]
    exact h.smul_residue_eq (IsLocalRing.residue A a)
  have h2 : g • a - a ^ q ∈ IsLocalRing.maximalIdeal A := by
    have h0 : IsLocalRing.residue A (g • a - a ^ q) = 0 := by
      rw [map_sub, h1, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hcoe : ((g • a - a ^ q : A) : L) = σ x - x ^ q := rfl
  have := (coe_mem_nonunits_iff (A := A)).mpr h2
  rwa [hcoe] at this

end Place

section PlaceIdeal

variable {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F] [Algebra F L]

theorem algebraMap_ringOfIntegers_mem (x : 𝓞 F) :
    algebraMap F L (algebraMap (𝓞 F) F x) ∈ A := by
  have hint : IsIntegral ℤ (algebraMap F L (algebraMap (𝓞 F) F x)) :=
    (RingOfIntegers.isIntegral_coe x).map ((algebraMap F L).toIntAlgHom)
  haveI : IsScalarTower ℤ A L := IsScalarTower.of_algebraMap_eq fun n => by
    simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  have hintA : IsIntegral A (algebraMap F L (algebraMap (𝓞 F) F x)) := hint.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA
  exact ha ▸ a.2

noncomputable def placeIdealHom : 𝓞 F →+* A :=
  ((algebraMap F L).comp (algebraMap (𝓞 F) F)).codRestrict A.toSubring
    (algebraMap_ringOfIntegers_mem A F)

theorem coe_placeIdealHom_apply (x : 𝓞 F) :
    (placeIdealHom A F x : L) = algebraMap F L (algebraMap (𝓞 F) F x) := rfl

noncomputable def placeIdeal : Ideal (𝓞 F) :=
  (IsLocalRing.maximalIdeal A).comap (placeIdealHom A F)

theorem mem_placeIdeal_iff {x : 𝓞 F} :
    x ∈ placeIdeal A F ↔ algebraMap F L (algebraMap (𝓞 F) F x) ∈ A.nonunits := by
  unfold placeIdeal
  rw [Ideal.mem_comap, ← coe_mem_nonunits_iff, coe_placeIdealHom_apply]

theorem placeIdeal_isPrime : (placeIdeal A F).IsPrime := by
  unfold placeIdeal
  haveI : (IsLocalRing.maximalIdeal A).IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  exact Ideal.IsPrime.comap _

variable {q : ℕ}

theorem natCast_mem_placeIdeal (hA : A.LiesOverPrime q) : (q : 𝓞 F) ∈ placeIdeal A F := by
  unfold placeIdeal
  rw [Ideal.mem_comap, map_natCast]
  exact natCast_mem_maximalIdeal A hA

theorem placeIdeal_ne_bot [NumberField F] (hq : q.Prime) (hA : A.LiesOverPrime q) :
    placeIdeal A F ≠ ⊥ := by
  intro hbot
  have hq0 : (q : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  exact hq0 (by simpa [hbot] using natCast_mem_placeIdeal A F hA)

theorem placeIdeal_isMaximal [NumberField F] (hq : q.Prime) (hA : A.LiesOverPrime q) :
    (placeIdeal A F).IsMaximal :=
  Ideal.IsPrime.isMaximal (placeIdeal_isPrime A F) (placeIdeal_ne_bot A F hq hA)

theorem placeIdeal_under_eq (hq : q.Prime) (hA : A.LiesOverPrime q) :
    (placeIdeal A F).under ℤ = FrobeniusDensity.ratPrimeIdeal q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h1 : FrobeniusDensity.ratPrimeIdeal q ≤ (placeIdeal A F).under ℤ := by
    rw [FrobeniusDensity.ratPrimeIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Ideal.under, Ideal.mem_comap]
    have hcast : algebraMap ℤ (𝓞 F) ((q : ℕ) : ℤ) = ((q : ℕ) : 𝓞 F) := by
      push_cast
      rfl
    rw [hcast]
    exact natCast_mem_placeIdeal A F hA
  have h2 : ((placeIdeal A F).under ℤ).IsPrime := by
    haveI := placeIdeal_isPrime A F
    rw [Ideal.under]
    exact Ideal.IsPrime.comap _
  exact ((FrobeniusDensity.isMaximal_ratPrimeIdeal q).eq_of_le h2.ne_top h1).symm

theorem placeIdeal_liesOver (hq : q.Prime) (hA : A.LiesOverPrime q) :
    (placeIdeal A F).LiesOver (FrobeniusDensity.ratPrimeIdeal q) :=
  ⟨(placeIdeal_under_eq A F hq hA).symm⟩

theorem card_quotient_under (hq : q.Prime) (hA : A.LiesOverPrime q) :
    Nat.card (ℤ ⧸ (placeIdeal A F).under ℤ) = q := by
  rw [placeIdeal_under_eq A F hq hA, FrobeniusDensity.ratPrimeIdeal, Nat.card_congr
    (Int.quotientSpanNatEquivZMod q).toEquiv, Nat.card_zmod]

end PlaceIdeal

section Restriction

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F : Type*) [Field F] [Algebra ℚ F] [Algebra F L] [IsScalarTower ℚ F L] [Normal ℚ F]
  [NumberField F]
variable (A : ValuationSubring L)

omit [NumberField F] in

theorem isArithFrobAt_restrictNormalHom {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : A.LiesOverPrime ℓ) {τ : L ≃ₐ[ℚ] L} (hτ : A.IsFrobeniusAt τ ℓ) :
    IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) (placeIdeal A F) := by
  intro x
  rw [card_quotient_under A F hℓ hA, mem_placeIdeal_iff]
  have hsmul : algebraMap (𝓞 F) F
      (MulSemiringAction.toAlgHom ℤ (𝓞 F) (AlgEquiv.restrictNormalHom F τ) x) =
      AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x) := rfl
  have hrestrict : algebraMap F L (AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x)) =
      τ (algebraMap F L (algebraMap (𝓞 F) F x)) := by
    have h : AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x)
        = τ.restrictNormal F (algebraMap (𝓞 F) F x) := rfl
    rw [h, AlgEquiv.restrictNormal_commutes]
  rw [map_sub, map_pow, map_sub, map_pow, hsmul, hrestrict]
  exact smul_sub_pow_mem_nonunits hτ (algebraMap_ringOfIntegers_mem A F x)

end Restriction

end FrobDictEngine

open scoped NumberField in
open FrobDictEngine in
theorem solution
    {L : Type*} [Field L] [Algebra ℚ L]
    (F : Type*) [Field F] [Algebra ℚ F] [NumberField F] [Algebra F L] [IsScalarTower ℚ F L]
    [Normal ℚ F]
    (A : ValuationSubring L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ)
    {τ : L ≃ₐ[ℚ] L} (hτ : A.IsFrobeniusAt τ ℓ) :
    ∃ Q : Ideal (𝓞 F),
      (∀ x : 𝓞 F, x ∈ Q ↔ algebraMap F L (algebraMap (𝓞 F) F x) ∈ A.nonunits) ∧
      Q.IsMaximal ∧ Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ) ∧ Finite (𝓞 F ⧸ Q) ∧
      IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) Q := by
  refine ⟨placeIdeal A F, fun x => mem_placeIdeal_iff A F, placeIdeal_isMaximal A F hℓ hA,
    placeIdeal_liesOver A F hℓ hA, ?_, isArithFrobAt_restrictNormalHom F A hℓ hA hτ⟩
  exact Ideal.finiteQuotientOfFreeOfNeBot _ (placeIdeal_ne_bot A F hℓ hA)

end S_ValuationSubring_exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt
end P2MW
export P2MW.S_ValuationSubring_exists_ideal_isArithFrobAt_restrictNormalHom_of_isFrobeniusAt (solution)
