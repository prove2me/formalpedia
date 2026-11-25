-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:02:44.804257+00:00
-- url     : https://prove2.me/submissions/9019bea0-bfb4-4f12-ac81-be1f276b4730

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_mulVec_apply_le_4c4c2f496192
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_inv_mulVec_mulVec_9949bf0822d2

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.HermNorm
theorem _root_.solution (h : HermNorm n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v := by
  refine ⟨∑ j, ∑ l, ‖h.mat⁻¹ j l‖, by positivity, fun v j => ?_⟩
  conv_lhs => rw [← h.li_inv_mulVec_mulVec v]
  calc ‖(h.mat⁻¹ *ᵥ (h.mat *ᵥ v)) j‖ = ‖∑ l, h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := rfl
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ * ‖(h.mat *ᵥ v) l‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp_rw [norm_mul]
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ * h.norm v :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h.li_norm_mulVec_apply_le v l)
          (_root_.norm_nonneg _)
    _ = (∑ l, ‖h.mat⁻¹ j l‖) * h.norm v := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ l, ‖h.mat⁻¹ j l‖) * h.norm v :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j => ∑ l, ‖h.mat⁻¹ j l‖)
          (fun j _ => by positivity) (Finset.mem_univ j)) (h.li_norm_nonneg v)
end GroundTheory.Heights₂.Heights.HermNorm
