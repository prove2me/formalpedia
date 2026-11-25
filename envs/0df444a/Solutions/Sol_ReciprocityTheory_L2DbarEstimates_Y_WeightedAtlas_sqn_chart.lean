-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:16.547269+00:00
-- url     : https://prove2.me/submissions/aa7bc46b-c692-4076-8cd7-b2598411216e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_chart_of_isSec

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
theorem _root_.solution {N : ℕ} (la : La) (w : Fin N → ι → Y → ℂ) (hw : ∀ k, A.IsSec la (w k)) (i : ι)
    {y : Y} (hy : y ∈ (A.chart i).source) :
    A.sqn la w y = (∑ k, ‖w k i y‖ ^ 2) * Real.exp (-A.ph la i y) := by
  unfold sqn
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => A.nsq_chart_of_isSec la (w k) (hw k) i hy
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
