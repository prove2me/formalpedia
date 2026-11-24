-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_graphPt_injective_of_graphBase_06146e145eca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:47.672019+00:00
-- url     : https://prove2.me/submissions/9b80eff7-958d-4e4f-8884-a9be0abefcc6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphBase_graphPt_3d0058ca640d

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
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) : Function.Injective (graphPt e F) :=
  Function.LeftInverse.injective (graphBase_graphPt e F)
end GroundTheory.Heights₂.Heights
