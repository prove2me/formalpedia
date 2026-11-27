-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaLinear_proof_4a19a2f41e3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:19.856434+00:00
-- url     : https://prove2.me/submissions/740df8b6-d7f7-42bf-afe2-bb02f5ee916c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaLinear_sqrt_det_adjoint_comp_eq_normDet_0d5987244845

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
open MeasureTheory Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace AreaLinear
theorem _root_.solution : AreaLinear.Statement := by
  intro k m L _ A
  have h := LinearMap.hausdorffMeasure_image L A
  rw [finrank_euclideanSpace_fin] at h
  rw [h, AreaLinear.sqrt_det_adjoint_comp_eq_normDet]
end AreaLinear
end GroundTheory.Heights₂.Heights
