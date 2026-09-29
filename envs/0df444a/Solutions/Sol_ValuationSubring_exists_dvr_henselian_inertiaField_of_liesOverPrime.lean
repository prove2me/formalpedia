-- Prove2me | solution 1 for ValuationSubring.exists_dvr_henselian_inertiaField_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8422d396-65b0-5563-8b9a-733648dd5f72

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_dvr_henselian_inertiaField_of_liesOverPrime
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

namespace UnramS1

open ValuationSubring

theorem isUnit_natCast_of_not_dvd (B : ValuationSubring (AlgebraicClosure ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hB : B.LiesOverPrime ℓ) {n : ℕ} (hn : ¬ ℓ ∣ n) : IsUnit ((n : ℕ) : ↥B) := by
  by_contra hu
  have hmem : ((n : ℕ) : ↥B) ∈ IsLocalRing.maximalIdeal ↥B := by
    rwa [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
  have hℓmem : ((ℓ : ℕ) : ↥B) ∈ IsLocalRing.maximalIdeal ↥B := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simp at hB ⊢
    exact hB
  have hcop : IsCoprime (ℓ : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hn)
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : ↥B) ∈ IsLocalRing.maximalIdeal ↥B := by
    have := congrArg (fun z : ℤ => ((z : ℤ) : ↥B)) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓmem) (Ideal.mul_mem_left _ _ hmem)
  exact (IsLocalRing.maximalIdeal.isMaximal ↥B).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

theorem exists_dvr_inertiaField (ℓ : ℕ) (hℓ : ℓ.Prime) (B : ValuationSubring (AlgebraicClosure ℚ)) (hBℓ : B.LiesOverPrime ℓ) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : HenselianLocalRing O)
      (_ : IsAlgClosed (IsLocalRing.ResidueField O)) (i : O →+* AlgebraicClosure ℚ),
      Function.Injective i ∧ (∀ r : O, i r ∈ B) ∧
      (∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ r : O, σ (i r) = i r) ∧
      (∀ n : ℕ, ¬ ℓ ∣ n → IsUnit ((n : ℕ) : O)) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField (B.inertiaSubgroupIn ℚ) with hF
  let O : ValuationSubring ↥F := B.comap (algebraMap ↥F (AlgebraicClosure ℚ))
  obtain ⟨hdvr, -, -, -⟩ := ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn B ℓ hBℓ
  have hhens : HenselianLocalRing ↥O :=
    ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) B
  have hres : IsAlgClosed (IsLocalRing.ResidueField ↥O) :=
    ValuationSubring.isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn B ℓ hBℓ ℚ
  let i : ↥O →+* AlgebraicClosure ℚ := (algebraMap ↥F (AlgebraicClosure ℚ)).comp O.subtype
  have hi_apply : ∀ r : ↥O, i r = ((r : ↥F) : AlgebraicClosure ℚ) := fun _ => rfl

  have hunit : ∀ n : ℕ, ¬ ℓ ∣ n → IsUnit ((n : ℕ) : ↥O) := by
    intro n hn
    have huB := isUnit_natCast_of_not_dvd B hℓ hBℓ hn
    have hn0 : ((n : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have : (n : ℕ) = 0 := by exact_mod_cast h0
      exact hn (this ▸ dvd_zero _)
    have hnF0 : ((n : ℕ) : ↥F) ≠ 0 := by
      intro h0; apply hn0
      have := congrArg (algebraMap ↥F (AlgebraicClosure ℚ)) h0
      simpa using this

    have hinvB : ((n : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ B := by
      obtain ⟨u, hu⟩ := huB
      have hval : ((u⁻¹ : (↥B)ˣ) : ↥B).val = ((n : ℕ) : AlgebraicClosure ℚ)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have := congrArg Subtype.val u.inv_mul
        simpa [hu] using this
      rw [← hval]; exact Subtype.mem _

    have hmemO : ((n : ℕ) : ↥F)⁻¹ ∈ O := by
      show algebraMap ↥F (AlgebraicClosure ℚ) (((n : ℕ) : ↥F)⁻¹) ∈ B
      rw [map_inv₀, map_natCast]; exact hinvB
    refine isUnit_iff_exists_inv.mpr ⟨⟨((n : ℕ) : ↥F)⁻¹, hmemO⟩, ?_⟩
    apply Subtype.ext
    simp [hnF0]
  refine ⟨↥O, inferInstance, inferInstance, hdvr, hhens, hres, i, ?_, ?_, ?_, hunit⟩
  · intro x y h
    apply Subtype.ext
    exact (algebraMap ↥F (AlgebraicClosure ℚ)).injective (by simpa [hi_apply] using h)
  · intro r; exact r.2
  · intro σ hσ r
    rw [hi_apply]
    exact (IntermediateField.mem_fixedField_iff _ _).mp (r : ↥F).2 σ hσ

end UnramS1

theorem solution (ℓ : ℕ) (hℓ : ℓ.Prime) (B : ValuationSubring (AlgebraicClosure ℚ)) (hBℓ : B.LiesOverPrime ℓ) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : HenselianLocalRing O)
      (_ : IsAlgClosed (IsLocalRing.ResidueField O)) (i : O →+* AlgebraicClosure ℚ),
      Function.Injective i ∧ (∀ r : O, i r ∈ B) ∧
      (∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ r : O, σ (i r) = i r) ∧
      (∀ n : ℕ, ¬ ℓ ∣ n → IsUnit ((n : ℕ) : O)) :=
  UnramS1.exists_dvr_inertiaField ℓ hℓ B hBℓ

end S_ValuationSubring_exists_dvr_henselian_inertiaField_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_dvr_henselian_inertiaField_of_liesOverPrime (solution)
