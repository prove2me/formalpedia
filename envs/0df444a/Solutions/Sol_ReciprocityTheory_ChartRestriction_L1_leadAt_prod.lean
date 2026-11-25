-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.leadAt_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:38.374264+00:00
-- url     : https://prove2.me/submissions/65426fb7-fd30-4d53-8288-b395049d1000

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LeadAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_leadAt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_leadAt_factor
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul
import Theorems.Thm_Formalism_LT_LTL_Cong_mul
import Theorems.Thm_Formalism_LT_LTL_Near_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {α : Type} (S : Finset α) (x : α → K) {A : PowerSeries K} (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) :
    ∃ i, i ≤ 2 * S.card ∧ LeadAt (∏ P ∈ S, (A - C (x P) * X ^ 2)) (∏ P ∈ S, max 1 ‖x P‖) i := by
  classical
  refine Finset.induction_on S ⟨0, le_rfl, by simpa using leadAt_one⟩ ?_
  intro a T ha ih
  obtain ⟨i, hi, h⟩ := ih
  obtain ⟨j, hj, h'⟩ := leadAt_factor hA hA0 (x a)
  refine ⟨j + i, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem ha]; omega
  · rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact h'.mul h
end ReciprocityTheory.ChartRestriction.L1
