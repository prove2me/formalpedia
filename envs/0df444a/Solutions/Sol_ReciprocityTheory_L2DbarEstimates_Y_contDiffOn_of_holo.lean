-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.contDiffOn_of_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:21.993812+00:00
-- url     : https://prove2.me/submissions/913b8384-bd9b-4310-a17e-74b8d84e4ffb

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
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ g U :=
  (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).restrict_scalars ℝ
end ReciprocityTheory.L2DbarEstimates.Y
