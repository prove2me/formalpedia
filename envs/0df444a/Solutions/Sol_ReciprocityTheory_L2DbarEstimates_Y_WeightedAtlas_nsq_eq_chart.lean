-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_eq_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:32.758855+00:00
-- url     : https://prove2.me/submissions/92722593-1fcb-4dd6-b48c-391ff141d657

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop

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
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold nsq
  set j := A.pick y
  have hj : y ∈ (A.chart j).source := A.mem_pick y
  have h1 : s i y = A.g la i j y * s j y := hs.2 i j y trivial hy hj
  have h2 : A.ph la j y = A.ph la i y - Real.log (‖A.g la i j y‖ ^ 2) := A.ph_trans la i j y hy hj
  have hg : 0 < ‖A.g la i j y‖ ^ 2 := by
    have := A.g_ne la i j y hy hj
    positivity
  rw [h1, h2, norm_mul, mul_pow, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
