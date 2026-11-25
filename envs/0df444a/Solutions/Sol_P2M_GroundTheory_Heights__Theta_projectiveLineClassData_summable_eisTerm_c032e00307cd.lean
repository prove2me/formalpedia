-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_summable_eisTerm_c032e00307cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:33.254838+00:00
-- url     : https://prove2.me/submissions/f49286fc-28c4-4a36-aa7d-1af81d4fe02f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eisTerm_nonneg_e6d069c6df72

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (τ : ℍ) {s : ℝ} (hs : 1 < s) : Summable (eisTerm τ s) := by
  have hk : 2 < 2 * s := by linarith
  have hsum := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
    (τ.im ^ s * EisensteinSeries.r τ ^ (-(2 * s)))
  rw [← (finTwoArrowEquiv ℤ).summable_iff]
  refine Summable.of_nonneg_of_le (fun x => eisTerm_nonneg τ s _) (fun x => ?_) hsum
  have hr := EisensteinSeries.r_pos τ
  simp only [Function.comp_apply, finTwoArrowEquiv_apply, eisTerm]
  split_ifs with hx
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg hr.le _))
      (Real.rpow_nonneg (norm_nonneg _) _)
  · have hb := EisensteinSeries.summand_bound τ (by linarith : (0 : ℝ) ≤ 2 * s) x
    rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _), mul_assoc]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg τ.im_pos.le _)
end GroundTheory.Heights₂.Theta.projectiveLineClassData
