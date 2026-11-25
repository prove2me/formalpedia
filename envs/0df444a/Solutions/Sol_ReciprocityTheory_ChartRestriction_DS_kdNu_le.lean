-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kdNu_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:14.837821+00:00
-- url     : https://prove2.me/submissions/a9ff62a8-e03c-4e80-941e-be1b86b26061

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_KDensC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {E X : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) (lam : Measure E) (c : ℝ≥0∞)
    (h : ∀ A ⊆ U, MeasurableSet A → m (f '' A) ≤ c * lam A) : kdNu m f U ≤ c • lam.restrict U := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [kdNu_apply hU hf hinj hA, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  exact h _ inter_subset_right (hA.inter hU)
end ReciprocityTheory.ChartRestriction.DS
