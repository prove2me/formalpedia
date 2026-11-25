-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.hyq_nsq_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:07.426181+00:00
-- url     : https://prove2.me/submissions/3d5cb61d-d870-4b9b-8514-4e47b34b2fd9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source)
    (hs : s i y = A.g la i (A.pick y) y * s (A.pick y) y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold WeightedAtlas.nsq
  have hp := A.mem_pick y
  have hg := A.g_ne la i (A.pick y) y hi hp
  have hpos : 0 < ‖A.g la i (A.pick y) y‖ ^ 2 := pow_pos (norm_pos_iff.2 hg) 2
  rw [A.ph_trans la i (A.pick y) y hi hp, hs, norm_mul, mul_pow]
  rw [show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) =
      -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add,
    Real.exp_log hpos]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
