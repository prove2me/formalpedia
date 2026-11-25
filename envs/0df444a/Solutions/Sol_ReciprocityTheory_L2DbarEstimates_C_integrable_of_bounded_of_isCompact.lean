-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.integrable_of_bounded_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:35.613504+00:00
-- url     : https://prove2.me/submissions/946fcce0-9c6b-408a-98dd-c949ce2a3369

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {T : Set (V n)} (hT : IsCompact T) {h : V n → ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict T)) {C : ℝ} (hb : ∀ z ∈ T, ‖h z‖ ≤ C)
    (h0 : ∀ z ∉ T, h z = 0) : Integrable h := by
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  haveI : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
  have hb' : ∀ᵐ z ∂(volume.restrict T), ‖h z‖ ≤ C :=
    (ae_restrict_iff' hTm).2 (Filter.Eventually.of_forall hb)
  have hon : IntegrableOn h T := by
    first
    | exact Integrable.of_bound hm C hb'
    | exact Integrable.of_bound hm hb'
    | exact Measure.integrableOn_of_bounded (M := C) hT.measure_lt_top.ne hm hb'
  have he : h = T.indicator h := by
    funext z
    by_cases hz : z ∈ T
    · simp [hz]
    · simp [hz, h0 z hz]
  rw [he]
  exact (integrable_indicator_iff hTm).2 hon
end ReciprocityTheory.L2DbarEstimates.C
