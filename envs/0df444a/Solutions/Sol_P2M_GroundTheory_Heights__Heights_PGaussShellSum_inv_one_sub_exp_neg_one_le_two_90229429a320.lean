-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussShellSum_inv_one_sub_exp_neg_one_le_two_90229429a320
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:58.135307+00:00
-- url     : https://prove2.me/submissions/bca92bcb-2984-4a8e-b4a7-76fc92c300af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussShellSum

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
open Real
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussShellSum
namespace GroundTheory.Heights₂.Heights.PGaussShellSum
theorem _root_.solution : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlt : 0 < 1 - Real.exp (-1) := by linarith
  rw [inv_le_comm₀ hlt (by norm_num)]
  linarith
end GroundTheory.Heights₂.Heights.PGaussShellSum
