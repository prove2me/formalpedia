-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_leviV_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:26:02.758598+00:00
-- url     : https://prove2.me/submissions/34a0d55f-08aa-4111-9733-43da56231dd7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


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
theorem _root_.solution (n : ℕ) (g₁ g₂ : V n → ℂ) (v : V n) (h : g₁ =ᶠ[𝓝 v] g₂)
    (ξ : Fin n → ℂ) : leviV n g₁ v ξ = leviV n g₂ v ξ := by
  unfold leviV
  have hk : ∀ k, wdb n k g₁ =ᶠ[𝓝 v] wdb n k g₂ := fun k =>
    h.eventuallyEq_nhds.mono fun y hy => by
      unfold wdb
      rw [hy.fderiv_eq (𝕜 := ℝ)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  unfold wd
  rw [(hk k).fderiv_eq (𝕜 := ℝ)]
end ReciprocityTheory.L2DbarEstimates.Y
