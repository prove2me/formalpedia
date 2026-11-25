-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_smooth_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:28:21.537261+00:00
-- url     : https://prove2.me/submissions/0a4b2f59-6133-4e70-9eac-d47e5f78aef7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (h : ∀ x, ∃ G : M → ℂ, Smooth n z G ∧ f =ᶠ[𝓝 x] G) : Smooth n z f := by
  intro e he y hy
  obtain ⟨G, hG, hfG⟩ := h (e.symm y)
  apply ContDiffAt.contDiffWithinAt
  have hGa : ContDiffAt ℝ ∞ (G ∘ e.symm) y := (hG e he).contDiffAt (e.open_target.mem_nhds hy)
  exact hGa.congr_of_eventuallyEq (hfG.comp_tendsto (e.continuousAt_symm hy))
end ReciprocityTheory.L2DbarEstimates.I
