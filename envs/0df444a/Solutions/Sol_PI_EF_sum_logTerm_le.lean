-- Prove2me | solution 1 for PI.EF.sum_logTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:50.229699+00:00
-- url     : https://prove2.me/submissions/82c04e45-21ae-4bb8-b766-0ac36fb470a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Theorems.Thm_PI_EF_sum_rpow_le
import Theorems.Thm_PI_EF_logTerm_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ n ∈ range K, logTerm (1 + 2 * ε) n ≤ 1 / ε ^ 2 := by
  have e0 : logTerm (1 + 2 * ε) 0 = 0 := by simp [logTerm]
  have e1 : logTerm (1 + 2 * ε) 1 = 0 := by simp [logTerm]
  have hb : ∀ i : ℕ, logTerm (1 + 2 * ε) (i + 2) ≤ ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
    intro i
    unfold logTerm
    push_cast
    have hx : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hl := Real.log_le_rpow_div hx.le hε
    have hp : 0 ≤ ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := Real.rpow_nonneg hx.le _
    calc Real.log ((i : ℝ) + 2) * ((i : ℝ) + 2) ^ (-(1 + 2 * ε))
        ≤ ((i : ℝ) + 2) ^ ε / ε * ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := mul_le_mul_of_nonneg_right hl hp
      _ = ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hx]
        congr 2
        ring
  calc ∑ n ∈ range K, logTerm (1 + 2 * ε) n
      ≤ ∑ n ∈ range (K + 2), logTerm (1 + 2 * ε) n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => logTerm_nonneg _ n)
    _ = ∑ i ∈ range K, logTerm (1 + 2 * ε) (i + 2) := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [zero_add, e0, e1, add_zero]
    _ ≤ ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := Finset.sum_le_sum fun i _ => hb i
    _ = (∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))) / ε := (Finset.sum_div _ _ _).symm
    _ ≤ (1 / ε) / ε := div_le_div_of_nonneg_right (sum_rpow_le hε K) hε.le
    _ = 1 / ε ^ 2 := by ring
end PI.EF
