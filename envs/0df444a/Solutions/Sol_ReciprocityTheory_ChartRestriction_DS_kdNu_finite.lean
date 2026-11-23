-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kdNu_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:25.824616+00:00
-- url     : https://prove2.me/submissions/8479ef39-f416-4b17-b04d-777def7f7eb3

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
theorem _root_.solution {m : Measure X} [IsFiniteMeasure m] {f : E → X} {U : Set E} (hU : MeasurableSet U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) : IsFiniteMeasure (kdNu m f U) :=
  ⟨by rw [kdNu_apply hU hf hinj MeasurableSet.univ]; exact measure_lt_top _ _⟩
end ReciprocityTheory.ChartRestriction.DS
