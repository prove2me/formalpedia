-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.holo_continuous_of_isLocalHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:30.331786+00:00
-- url     : https://prove2.me/submissions/3c5f7fa9-56a9-49af-a9b4-9b22f73e09df

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocallyCompactSpaceOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ)
    (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Holo n z f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hx' : e x ∈ e.target := e.map_source hx
  have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
    (hf e he).continuousOn.continuousAt (e.open_target.mem_nhds hx')
  have h3 : ContinuousAt ((f ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hx)
  refine h3.congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  show f (e.symm (e y)) = f y
  rw [e.left_inv hy]
end ReciprocityTheory.L2DbarEstimates.I
