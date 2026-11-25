-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.lintegral_vol_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:39.732697+00:00
-- url     : https://prove2.me/submissions/32c093f9-633d-421b-8a4e-d76da476ccea

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℝ≥0∞) (hf : Measurable f) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫⁻ x, f x ∂vol n z = ∫⁻ y in e.target, f (e.symm y) := by
  have h1 : ∫⁻ x, f x ∂vol n z = ∫⁻ x in e.source, f x ∂vol n z := by
    rw [← lintegral_indicator e.open_source.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ e.source
    · simp [Set.indicator_apply, hx]
    · simp [Set.indicator_apply, hx, hs x hx]
  rw [h1, vol_restrict_source n z hz e he,
    lintegral_map' hf.aemeasurable (e.continuousOn_symm.aemeasurable e.open_target.measurableSet)]
end ReciprocityTheory.L2DbarEstimates
