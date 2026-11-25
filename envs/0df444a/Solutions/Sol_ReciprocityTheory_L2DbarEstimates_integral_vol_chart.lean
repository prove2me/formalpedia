-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integral_vol_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:21:30.556173+00:00
-- url     : https://prove2.me/submissions/b88ed5b7-584c-4ab9-a486-e7aab9ab08db

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_restrict_source

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℂ) (hf : Measurable f) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫ x, f x ∂vol n z = ∫ y in e.target, f (e.symm y) := by
  have h1 : ∫ x, f x ∂vol n z = ∫ x in e.source, f x ∂vol n z := by
    rw [← integral_indicator e.open_source.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ e.source
    · simp [Set.indicator_apply, hx]
    · simp [Set.indicator_apply, hx, hs x hx]
  rw [h1, vol_restrict_source n z hz e he,
    integral_map (e.continuousOn_symm.aemeasurable e.open_target.measurableSet)
      hf.aestronglyMeasurable]
end ReciprocityTheory.L2DbarEstimates
