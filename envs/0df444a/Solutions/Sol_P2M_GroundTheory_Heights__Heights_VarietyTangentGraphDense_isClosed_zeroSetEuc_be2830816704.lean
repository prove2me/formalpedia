-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_isClosed_zeroSetEuc_be2830816704
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:22:59.475531+00:00
-- url     : https://prove2.me/submissions/dcf2b84b-463e-4325-807e-e46a514b4cdc

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_continuous_eval_c29a4cd0acc4


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
theorem _root_.solution {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSetEuc J) := by
  have h : zeroSetEuc J = ⋂ q ∈ J, {z : EuclideanSpace ℂ (Fin n) | eval (fun i => z i) q = 0} := by
    ext z
    simp [zeroSetEuc]
  rw [h]
  refine isClosed_biInter fun q _ => isClosed_eq ?_ continuous_const
  exact (MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)
end GroundTheory.Heights₂.Heights.VarietyTangentGraphDense
