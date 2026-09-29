-- Prove2me | solution 1 for ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/40a9e6bc-d48e-53cf-aeb6-951fae5ea3cd

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

private theorem TK_tameCharacter_at_one (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    A.tameCharacter 1 σ = 1 := by
  have h : σ 1 / 1 ∈ A := by rw [map_one, div_one]; exact one_mem A
  rw [ValuationSubring.tameCharacter, dif_pos h]
  have h1 : (⟨σ 1 / 1, h⟩ : ↥A) = 1 := Subtype.ext (by simp)
  rw [h1, map_one]

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
      ∃ a : (↥A)ˣ, ((a : ↥A) : AlgebraicClosure ℚ) * z = σ z ∧
        IsLocalRing.residue (↥A) (a : ↥A) = A.tameCharacter z σ) ∧
    ∀ u : (↥A)ˣ, A.tameCharacter ((u : ↥A) : AlgebraicClosure ℚ) σ = 1 := by

  obtain ⟨τ, _, hτ⟩ := Subgroup.mem_map.mp hσ
  have hd : σ ∈ A.decompositionSubgroup ℚ := by rw [← hτ]; exact τ.2
  refine ⟨fun z hz => ?_, fun u => ?_⟩
  · have hσz : σ z ≠ 0 := (map_ne_zero σ).mpr hz
    have hv : A.valuation (σ z) = A.valuation z :=
      ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A hd z
    have hvz : A.valuation z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
    have hvσz : A.valuation (σ z) ≠ 0 := (Valuation.ne_zero_iff _).mpr hσz
    have hmem : σ z / z ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_div₀, hv, div_self hvz])
    have hmem' : z / σ z ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_div₀, hv, div_self hvz])
    let a : (↥A)ˣ :=
      ⟨⟨σ z / z, hmem⟩, ⟨z / σ z, hmem'⟩,
        Subtype.ext (show σ z / z * (z / σ z) = 1 by
          rw [div_mul_div_comm, mul_comm z (σ z), div_self (mul_ne_zero hσz hz)]),
        Subtype.ext (show z / σ z * (σ z / z) = 1 by
          rw [div_mul_div_comm, mul_comm (σ z) z, div_self (mul_ne_zero hz hσz)])⟩
    refine ⟨a, ?_, ?_⟩
    · show σ z / z * z = σ z
      exact div_mul_cancel₀ (σ z) hz
    · rw [ValuationSubring.tameCharacter, dif_pos hmem]
  · have hvu : A.valuation ((u : ↥A) : AlgebraicClosure ℚ) = 1 := A.valuation_unit u
    have hu0 : ((u : ↥A) : AlgebraicClosure ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hvu]; exact one_ne_zero)
    have hu : ((u : ↥A) : AlgebraicClosure ℚ) / 1 ∈ A := by rw [div_one]; exact (u : ↥A).2
    have hu' : 1 / ((u : ↥A) : AlgebraicClosure ℚ) ∈ A :=
      (A.valuation_le_one_iff _).mp (by rw [map_div₀, map_one, hvu, div_one])
    rw [ValuationSubring.tameCharacter_eq_of_div_mem_of_div_mem A 1 ((u : ↥A) : AlgebraicClosure ℚ) one_ne_zero hu0 hu hu' hσ]
    exact TK_tameCharacter_at_one A σ

#print axioms solution

end S_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn (solution)
