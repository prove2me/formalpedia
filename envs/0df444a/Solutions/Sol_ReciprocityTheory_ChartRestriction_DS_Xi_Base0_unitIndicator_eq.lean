-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.unitIndicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:54.456256+00:00
-- url     : https://prove2.me/submissions/8c29c699-db2b-40fa-a8cc-f0e72e988e0b

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
theorem _root_.solution {y : ℝ} (hy : |y| ≤ 1) : one1 y = 1 := by
  unfold one1
  rw [Set.indicator_of_mem (show y ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hy)]
  try rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
