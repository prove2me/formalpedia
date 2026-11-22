-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.tW_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:16.532502+00:00
-- url     : https://prove2.me/submissions/09a74bec-3cee-46d8-b270-fe762ca20a70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (q : ι) (x : ι → ℂ) :
    tW q x ^ 2 = ∑ i, Complex.normSq (x i) - Complex.normSq (x q) := by
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg])]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne',
    Finset.sum_erase_eq_sub (Finset.mem_univ q)]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
