-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuousOn_graphPt_d41269ebec60
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:55.496383+00:00
-- url     : https://prove2.me/submissions/9d876f5d-9215-425a-9412-16ad72781ad9

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
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)} {Ω : Set (EuclideanSpace ℂ (Fin d))}
    (hF : ContinuousOn F Ω) : ContinuousOn (graphPt e F) Ω := by
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun j => ?_)
  rcases e j with i | i
  · exact ((PiLp.continuous_apply 2 _ i)).continuousOn
  · exact (PiLp.continuous_apply 2 _ i).comp_continuousOn hF
end GroundTheory.Heights₂.Heights
