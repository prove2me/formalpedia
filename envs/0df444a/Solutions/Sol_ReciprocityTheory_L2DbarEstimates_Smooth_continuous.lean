-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Smooth.continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:04.727588+00:00
-- url     : https://prove2.me/submissions/febcd718-711a-4d32-9fb5-0f8fbe269960

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
namespace Smooth
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Smooth n z f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
    (hf e he).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  refine (h1.comp (e.continuousAt hx)).congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.left_inv hy]
end Smooth
end ReciprocityTheory.L2DbarEstimates
