-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_arithDegree_integers_b696023dcbfa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:44.938379+00:00
-- url     : https://prove2.me/submissions/ff5a4a06-f9e1-45fa-a63f-2bd38e7be46e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact

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
theorem _root_.solution : (HermitianBundle.integers K).arithDegree = 0 :=
  GroundTheory.Heights₂.Heights.arithDegree_integers
end HermitianBundle
end GroundTheory.Heights₂.Heights
