-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_s_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:32.066804+00:00
-- url     : https://prove2.me/submissions/b23baf8c-8b98-4084-867c-7fb5be63614b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_eq_chart


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
theorem _root_.solution (A : WeightedAtlas n Y ι La) {L : La} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) {i : ι} {x : Y} (hx : x ∈ (A.chart i).source)
    (hw : w0 i x ≠ 0) :
    A.sqn L s x = ‖w0 i x‖ ^ 2 * Real.exp (-A.ph L i x) * ‖A.zLoc w0 s i (A.chart i x)‖ ^ 2 := by
  unfold sqn
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [A.nsq_eq_chart (hs k) hx]
  simp only [zLoc, PiLp.toLp_apply, (A.chart i).left_inv hx, norm_div, div_pow]
  have : ‖w0 i x‖ ^ 2 ≠ 0 := by positivity
  field_simp
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
