-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.phiC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:40:39.797578+00:00
-- url     : https://prove2.me/submissions/fbb9be38-e472-4cc1-8db2-d58c984457d6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_measurable_indicator_usc
import Theorems.Thm_ReciprocityTheory_AnForm_A_isPsh_locallyIntegrable_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : IsPsh U φ) {C : Set (Fin D → ℂ)} (hC : IsCompact C)
    (hCU : C ⊆ U) : Measurable (C.indicator φ) ∧ Integrable (C.indicator φ) := by
  have e : C.indicator φ = C.indicator (U.indicator φ) := by
    ext x
    by_cases hx : x ∈ C
    · simp [hx, hCU hx]
    · simp [hx]
  refine ⟨e ▸ (measurable_indicator_usc hU hφ.1).indicator hC.isClosed.measurableSet, ?_⟩
  exact (integrable_indicator_iff hC.isClosed.measurableSet).2
    ((isPsh_locallyIntegrable_thm D U φ hU hφ).integrableOn_compact_subset hCU hC)
end ReciprocityTheory.AnForm.A
