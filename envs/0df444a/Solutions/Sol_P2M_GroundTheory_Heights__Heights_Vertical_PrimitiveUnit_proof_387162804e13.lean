-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_PrimitiveUnit_proof_387162804e13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:54.136994+00:00
-- url     : https://prove2.me/submissions/78e7b864-8d65-43ff-bfc1-3d4ab137ccd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PPrimitiveUnit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_not_unit_of_pow_succ_d05b5f3dd358

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace PrimitiveUnit
theorem _root_.solution : PrimitiveUnit.Statement := by
  intro R F _ _ _ _ _ _ σ p q c ⟨m0, hm0⟩ ⟨m1, hm1⟩ hpq
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsF : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have key : ∀ m, s * p.coeff m = a * q.coeff m := by
    intro m
    have h := congrArg (coeff m) hpq
    rw [coeff_map, coeff_C_mul, coeff_map] at h
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, h]
    field_simp
  have ha0 : a ≠ 0 := by
    intro ha
    have h := key m0
    rw [ha, zero_mul] at h
    exact hm0.ne_zero ((mul_eq_zero.mp h).resolve_left hs0)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨i, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨j, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
      exact not_unit_of_pow_succ hϖ u₁ u₂ i d hm1 (key m1)
    · exact h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, i = j + d + 1 := ⟨i - j - 1, by omega⟩
      exact not_unit_of_pow_succ hϖ u₂ u₁ j d hm0 (key m0).symm
  subst hij
  refine ⟨u₁ * u₂⁻¹, ?_⟩
  rw [div_eq_iff hsF, ← map_mul]
  congr 1
  rw [Units.val_mul, mul_assoc, ← mul_assoc ((u₂⁻¹ : Rˣ) : R), Units.inv_mul, one_mul]
end PrimitiveUnit
end GroundTheory.Heights₂.Heights.Vertical
