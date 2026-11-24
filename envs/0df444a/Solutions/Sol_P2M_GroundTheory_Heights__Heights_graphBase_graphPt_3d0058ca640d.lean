-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_graphBase_graphPt_3d0058ca640d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:49.791751+00:00
-- url     : https://prove2.me/submissions/15f1c13b-bfd5-4a60-9057-6d4d0228560b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre

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
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) (x : EuclideanSpace ℂ (Fin d)) :
    graphBase e (graphPt e F x) = x := by
  ext i
  simp [graphBase, graphPt]
end GroundTheory.Heights₂.Heights
