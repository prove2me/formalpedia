-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_fsLog_nrmv_nonpos_006a7a1e23fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:48.921682+00:00
-- url     : https://prove2.me/submissions/67f20dc8-ce29-445b-924f-ca5ad313f0b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanLinearBall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_dualNorm_06ad3d73255e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_nrmv_le_0587e199c44b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_norm_sum_mul_le_df0c9fbe6d51

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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanLinearBall
namespace GroundTheory.Heights₂.Heights.SphereMeanLinearBall
theorem _root_.solution (n : ℕ) (y w : Fin n → ℂ) :
    fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0 := by
  rw [fsLog, std_dualNorm]
  refine Real.log_nonpos (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) ?_
  refine div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)
  refine (norm_sum_mul_le n _ _).trans ?_
  have h1 : √(∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact sum_sq_nrmv_le n w
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h1
end GroundTheory.Heights₂.Heights.SphereMeanLinearBall
