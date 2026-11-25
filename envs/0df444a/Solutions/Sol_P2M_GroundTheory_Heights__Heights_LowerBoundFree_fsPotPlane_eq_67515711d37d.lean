-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsPotPlane_eq_67515711d37d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:39.592147+00:00
-- url     : https://prove2.me/submissions/e8a9ded9-bf8b-4913-a727-b5a25c182b43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianLogGrowth

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {y : ℂ} (hy : 1⁻¹ < ‖y‖) : fsPotPlane y = 1 * Real.log ‖y‖ + fsPotPlane y⁻¹ := by
  have hy0 : 0 < ‖y‖ := lt_trans (by norm_num) hy
  unfold fsPotPlane
  rw [norm_inv]
  have h1 : 1 + ‖y‖ ^ 2 = ‖y‖ ^ 2 * (1 + ‖y‖⁻¹ ^ 2) := by
    field_simp
    ring
  rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree
