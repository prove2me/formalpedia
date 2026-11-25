-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.ae_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:35.686749+00:00
-- url     : https://prove2.me/submissions/93e151cb-78e0-4d63-af8e-45d606a9327d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_volume_bad

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
theorem _root_.solution : ∀ᵐ x : ι → ℂ, ∀ i, (x i).im ≠ 0 ∧ (x i).re ≠ 0 := by
  rw [ae_iff]
  have h := volume_bad ι
  convert h using 2
  ext x
  simp only [Set.mem_setOf_eq, not_forall, not_and_or, ne_eq, not_not]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
