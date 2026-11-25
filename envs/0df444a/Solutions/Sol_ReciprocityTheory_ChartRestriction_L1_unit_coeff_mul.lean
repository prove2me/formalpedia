-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.unit_coeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:59.907239+00:00
-- url     : https://prove2.me/submissions/d14fe528-123a-4d14-b10e-a46f85be5561

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
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
theorem _root_.solution {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g)
    (hf0 : ‖constantCoeff f‖ = 1) (N : ℕ) (h : ∃ i, i ≤ N ∧ ‖coeff i g‖ = 1) :
    ∃ i, i ≤ N ∧ ‖coeff i (f * g)‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  obtain ⟨i₀, hmin, hl⟩ := leadAt_first_unit hg ⟨i, hi⟩
  have hf' : LeadAt f 1 0 := ⟨one_pos, hf, fun n hn => absurd hn (Nat.not_lt_zero _),
    by rw [coeff_zero_eq_constantCoeff_apply, hf0]⟩
  have hm := hf'.mul hl
  refine ⟨0 + i₀, by have := hmin i hi; omega, ?_⟩
  rw [hm.2.2.2, one_mul]
end ReciprocityTheory.ChartRestriction.L1
