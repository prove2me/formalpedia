-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Ck.continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:04.76517+00:00
-- url     : https://prove2.me/submissions/b66b8458-2a45-4a71-86ad-4560ccd43ec6

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
namespace Ck
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
    (hf e he).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  refine (h1.comp (e.continuousAt hx)).congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.left_inv hy]
end Ck
end ReciprocityTheory.L2DbarEstimates
