-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_continuousOn_ratMap_aee27c8cf252
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:04.38138+00:00
-- url     : https://prove2.me/submissions/4c2899a7-b10e-482c-ba0b-4c433717f2af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetNoChartNull
theorem _root_.solution (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} :=
  continuousOn_pi.2 fun r =>
    (MvPolynomial.continuous_eval (p r)).continuousOn.div (MvPolynomial.continuous_eval q).continuousOn
      fun _ hx => hx
end GroundTheory.Heights₂.Heights.RatSheetNoChartNull
