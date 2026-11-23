-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.dot_star_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:33.897169+00:00
-- url     : https://prove2.me/submissions/dc192bb4-3b37-4ad6-aa8c-9b24e38ba637

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
theorem _root_.solution (y : ι → ℂ) : star y ⬝ᵥ y = ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
