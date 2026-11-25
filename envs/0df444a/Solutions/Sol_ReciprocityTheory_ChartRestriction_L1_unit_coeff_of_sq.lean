-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.unit_coeff_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:03.55804+00:00
-- url     : https://prove2.me/submissions/f02aeeb4-1215-447b-b8fc-649a4bbb81b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_gauss_norm_sum_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LeadAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_leadAt_first_unit
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
theorem _root_.solution {e : PowerSeries K} (he : IntegralPS e) (N : ℕ)
    (h : ∃ i, i ≤ 2 * N ∧ ‖coeff i (e ^ 2)‖ = 1) : ∃ i, i ≤ N ∧ ‖coeff i e‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  have hex : ∃ j, ‖coeff j e‖ = 1 := by
    by_contra hno
    push Not at hno
    have hlt : ∀ n, ‖coeff n e‖ < 1 := fun n => lt_of_le_of_ne (he n) (hno n)
    have : ‖coeff i (e ^ 2)‖ < 1 := by
      rw [sq, coeff_mul]
      refine gauss_norm_sum_lt _ _ one_pos fun x _ => ?_
      rw [norm_mul]
      calc ‖coeff x.1 e‖ * ‖coeff x.2 e‖ ≤ ‖coeff x.1 e‖ * 1 :=
            mul_le_mul_of_nonneg_left (he _) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hlt _
    exact this.ne hi
  obtain ⟨j, -, hl⟩ := leadAt_first_unit he hex
  have hm := hl.mul hl
  rw [one_mul, ← sq] at hm
  refine ⟨j, ?_, hl.2.2.2⟩
  by_contra hc
  push Not at hc
  exact (hm.2.2.1 i (by omega)).ne hi
end ReciprocityTheory.ChartRestriction.L1
