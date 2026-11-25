-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_wd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:26:06.530847+00:00
-- url     : https://prove2.me/submissions/f5d37779-f55b-41ec-87f0-04b296e6a43c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open Filter Topology Set ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (n : ℕ) (j : Fin n) {ι : Type*} (s : Finset ι) (f : ι → V n → ℂ) (v : V n)
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) v) :
    wd n j (fun y => ∑ a ∈ s, f a y) v = ∑ a ∈ s, wd n j (f a) v := by
  unfold wd
  have e : (fun y => ∑ a ∈ s, f a y) = ∑ a ∈ s, f a := by
    funext y
    simp
  rw [e, fderiv_sum hf]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
end ReciprocityTheory.L2DbarEstimates.Y
