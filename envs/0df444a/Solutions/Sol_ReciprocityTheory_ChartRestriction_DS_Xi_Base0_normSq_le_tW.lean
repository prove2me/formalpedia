-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.normSq_le_tW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:46.752974+00:00
-- url     : https://prove2.me/submissions/bc411ca5-351a-490b-8aca-f549336e3b0b

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
theorem _root_.solution (q : ι) (x : ι → ℂ) (i : ι) (hi : i ≠ q) : Complex.normSq (x i) ≤ tW q x ^ 2 := by
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j)) := by
    intro j _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg hnn)]
  have h1 := Finset.single_le_sum hnn (Finset.mem_univ i)
  simpa [hi] using h1
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
