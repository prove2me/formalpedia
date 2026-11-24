-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_eval__algebraMap_3e6113ca9a3f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:43.677799+00:00
-- url     : https://prove2.me/submissions/5fa80566-df90-4cc7-aa12-08badacb8140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCompletionNormalDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open AdicCompletion Polynomial
variable {R : Type} [CommRing R] (J : Ideal R)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CompletionNormalDescent
theorem _root_.solution (n : ℕ) (x : R) :
    evalₐ J n (algebraMap R (AdicCompletion J R) x) = Ideal.Quotient.mk (J ^ n) x := by
  rw [(evalₐ J n).commutes]
  rfl
end CompletionNormalDescent
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
