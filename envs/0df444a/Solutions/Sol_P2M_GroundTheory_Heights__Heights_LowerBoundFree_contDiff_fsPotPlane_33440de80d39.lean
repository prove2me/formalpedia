-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_contDiff_fsPotPlane_33440de80d39
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:25.141088+00:00
-- url     : https://prove2.me/submissions/c3e934ac-92a2-4806-a8bc-d966b92b48b8

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
theorem _root_.solution : ContDiff ℝ 2 fsPotPlane := by
  unfold fsPotPlane
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).log fun y => by positivity).div_const _
end GroundTheory.Heights₂.Heights.LowerBoundFree
