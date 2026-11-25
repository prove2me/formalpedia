-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.gauss_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:28.491804+00:00
-- url     : https://prove2.me/submissions/73b142a2-4956-4a8a-a896-bd730940b8c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LeadAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_leadAt_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_leadAt_prod
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
theorem _root_.solution {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K)
    (hG : IntegralPS (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))) :
    ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨i, -, h⟩ := leadAt_prod S x hA hA0
  have hl := (leadAt_C hc).mul h
  rw [← hl.2.2.2]
  exact hG _
end ReciprocityTheory.ChartRestriction.L1
