-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.nsq_eq_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:29.372074+00:00
-- url     : https://prove2.me/submissions/644ebb83-acd4-480c-8b03-9b7c55c5b293

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (hF : A.IsSec la F)
    (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) :
    A.nsq la F y = ‖F i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold nsq
  have hj : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have htr := hF.2 i (A.pick y) y (Set.mem_univ _) hy hj
  have hph := A.ph_trans la i (A.pick y) y hy hj
  have hg := A.g_ne la i (A.pick y) y hy hj
  have hgp : 0 < ‖A.g la i (A.pick y) y‖ ^ 2 := by positivity
  have he : Real.exp (-(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2))) =
      ‖A.g la i (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    rw [show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) =
      -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add,
      Real.exp_log hgp]
    ring
  rw [hph, he, htr, norm_mul, mul_pow]
  ring
end ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
