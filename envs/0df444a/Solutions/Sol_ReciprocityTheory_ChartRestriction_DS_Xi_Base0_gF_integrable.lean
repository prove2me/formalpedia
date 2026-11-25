-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.gF_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:07.648431+00:00
-- url     : https://prove2.me/submissions/fc09c48b-15f0-44c1-9c6d-df6051897564

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_integrable_unitIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_integrable_powIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_integrable_reim

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
theorem _root_.solution (p q : ι) {β : ℝ} (hβ : β < 1) (i : ι) : Integrable (gF p q β i) := by
  by_cases h1 : i = q
  · have he : gF p q β i = fun z => one1 z.re * one1 z.im := by
      funext z
      simp [gF, h1]
    rw [he]
    exact integrable_reim integrable_unitIndicator integrable_unitIndicator
  · by_cases h2 : i = p
    · have h1' : p ≠ q := by
        rw [← h2]
        exact h1
      have he : gF p q β i = fun z => one1 z.re * pw1 β z.im := by
        funext z
        simp [gF, h2, h1']
      rw [he]
      exact integrable_reim integrable_unitIndicator (integrable_powIndicator hβ)
    · have he : gF p q β i = fun z => pw1 β z.re * pw1 β z.im := by
        funext z
        simp [gF, h1, h2]
      rw [he]
      exact integrable_reim (integrable_powIndicator hβ) (integrable_powIndicator hβ)
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
