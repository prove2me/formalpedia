-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentJacCompress_proof_6c5bd3592131
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:17:17.307196+00:00
-- url     : https://prove2.me/submissions/25913c47-786f-488a-a3bb-9fc041281af8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacCompress
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_starProjection_compress_4e477f7e7cd3

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
open Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TangentJacCompress
theorem _root_.solution : TangentJacCompress.Statement := by
  intro n m π T
  unfold tangentJac
  have h := LinearMap.normDet_sq (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype)
  exact h.trans (det_starProjection_compress (LinearMap.toContinuousLinearMap (linProjₗ π)) T).symm
end TangentJacCompress
end GroundTheory.Heights₂.Heights
