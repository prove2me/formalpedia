-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:27.446665+00:00
-- url     : https://prove2.me/submissions/fe238582-d845-499b-b5f8-3de35cadba6d

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
theorem _root_.solution (q : ι) (f : ι → ℝ) : ∑ i, f i = f q + ∑ i, (if i = q then 0 else f i) := by
  have hs : ∀ i, f i = (if i = q then f i else 0) + (if i = q then 0 else f i) := by
    intro i
    split_ifs <;> simp
  calc ∑ i, f i = ∑ i, ((if i = q then f i else 0) + (if i = q then 0 else f i)) :=
        Finset.sum_congr rfl (fun i _ => hs i)
    _ = f q + ∑ i, (if i = q then 0 else f i) := by
        first
        | (rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp)
        | simp [Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
