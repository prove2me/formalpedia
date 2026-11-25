-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_frameProjCLM_apply_b4ab43f50eca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:29.546846+00:00
-- url     : https://prove2.me/submissions/90aa0b1c-e22c-41d3-b7d5-5d78a719d57e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyTangentGraphDense

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
open MvPolynomial Topology Filter MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
namespace GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
theorem _root_.solution {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : frameProjCLM b I z = frameProj b I z := by
  funext i
  simp [frameProjCLM, frameProj]
end GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
