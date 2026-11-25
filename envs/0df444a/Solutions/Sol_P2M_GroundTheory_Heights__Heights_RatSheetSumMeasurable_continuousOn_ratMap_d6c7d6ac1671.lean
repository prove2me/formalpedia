-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_continuousOn_ratMap_d6c7d6ac1671
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:07.122162+00:00
-- url     : https://prove2.me/submissions/dba452ad-5bbe-47b5-a6e8-073c7be9f887

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
open GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
theorem _root_.solution (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {z | eval z q ≠ 0} := by
  show ContinuousOn (fun z r => eval z (p r) / eval z q) _
  exact continuousOn_pi.2 fun r => (MvPolynomial.continuous_eval (p r)).continuousOn.div
    (MvPolynomial.continuous_eval q).continuousOn fun z hz => hz
end GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
