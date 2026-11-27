-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_heightMetricChange_8390543b9bc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:44.295485+00:00
-- url     : https://prove2.me/submissions/30369efb-9ccc-4572-b13b-d51bd0024146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sigma_mem_points_5c3b047266ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : HeightMetricChange.Statement := by
  intro ι _ _ n P A A' hdeg B hB x hx
  have key : height A x - height A' x =
      ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
        ∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) -
          Real.log (A'.metric fun k i ↦ σ (coordVec x k i))) := by
    unfold height
    rw [hdeg, Finset.sum_sub_distrib]
    ring
  have hpos : (0 : ℝ) < Module.finrank ℚ (coordField x) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := coordField x)
  rw [key, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  have hs : |∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) -
      Real.log (A'.metric fun k i ↦ σ (coordVec x k i)))| ≤
      Module.finrank ℚ (coordField x) * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ B fun σ _ ↦ hB _ (sigma_mem_points P hx σ)).trans ?_
    rw [Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  calc _ ≤ ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ * (Module.finrank ℚ (coordField x) * B) :=
        mul_le_mul_of_nonneg_left hs (inv_pos.mpr hpos).le
    _ = B := by field_simp
end GroundTheory.Heights₂.Heights
