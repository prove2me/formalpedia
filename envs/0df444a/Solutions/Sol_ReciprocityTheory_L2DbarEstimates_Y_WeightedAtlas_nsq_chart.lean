-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:41:34.021958+00:00
-- url     : https://prove2.me/submissions/dd9b7841-4970-4a32-96ad-4128e9d95313

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_g_mul_g

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (la : La) (s : ι → Y → ℂ) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source)
    (hs : s (A.pick y) y = A.g la (A.pick y) i y * s i y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  have hp := A.mem_pick y
  unfold nsq
  rw [hs, A.ph_trans la i (A.pick y) y hy hp]
  have h1 := A.g_mul_g la (A.pick y) i hp hy
  have hgn : ‖A.g la i (A.pick y) y‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la i _ y hy hp)
  have hn : ‖A.g la (A.pick y) i y‖ ^ 2 * ‖A.g la i (A.pick y) y‖ ^ 2 = 1 := by
    rw [← mul_pow, ← norm_mul, h1, norm_one, one_pow]
  rw [neg_sub, Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, norm_mul, mul_pow,
    div_eq_mul_inv]
  linear_combination (‖s i y‖ ^ 2 * (Real.exp (A.ph la i y))⁻¹) * hn
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
