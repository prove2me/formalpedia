-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_two_of_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:27.18449+00:00
-- url     : https://prove2.me/submissions/fe897dc0-02e0-497e-be29-6d59f7fd265c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {v : V n} (hv : v ∈ U) : ContDiffAt ℂ 2 g v :=
  ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hv)).of_le (by norm_cast)
end ReciprocityTheory.L2DbarEstimates.Y
