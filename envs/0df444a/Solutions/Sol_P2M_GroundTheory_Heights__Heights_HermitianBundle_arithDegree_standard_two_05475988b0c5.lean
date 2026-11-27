-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_arithDegree_standard_two_05475988b0c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:55:23.687507+00:00
-- url     : https://prove2.me/submissions/85345439-ac9b-4720-8271-4a63f32a059c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_arithDegree_eq_add_d3246defcd21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_arithDegree_integers_b696023dcbfa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
namespace HermitianBundle
theorem _root_.solution : (HermitianBundle.standard K 2).arithDegree = 0 := by
  rw [(HermitianExtension.standardSplit K).arithDegree_eq_add,
    HermitianBundle.arithDegree_integers, add_zero]
end HermitianBundle
end GroundTheory.Heights₂.Heights
