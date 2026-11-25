-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_realEisenstein_nonneg_23a9db672901
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:42.906862+00:00
-- url     : https://prove2.me/submissions/59e6fe54-5061-4eef-aa77-5f81df2da18d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg

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
open UpperHalfPlane
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (τ : ℍ) (s : ℝ) : 0 ≤ realEisenstein τ s := by
  refine tsum_nonneg fun p => ?_
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _)
end GroundTheory.Heights₂.Theta
