-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.measurableSet_Bset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:34.472697+00:00
-- url     : https://prove2.me/submissions/125c4e10-f76a-4e90-9504-745fa73be961

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (q : ι) : MeasurableSet (Bset q) := by
  have hc : Continuous (tW q) := by
    unfold tW
    refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
    by_cases h : i = q
    · simp only [h, if_true]
      exact continuous_const
    · simp only [h, if_false]
      exact Complex.continuous_normSq.comp (continuous_apply i)
  have hn : Continuous (fun x : ι → ℂ => ‖x q‖) := continuous_norm.comp (continuous_apply q)
  unfold Bset
  exact (measurableSet_le measurable_const hc.measurable).inter
    ((measurableSet_le hc.measurable measurable_const).inter
      (measurableSet_le hn.measurable measurable_const))
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
