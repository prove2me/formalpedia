-- Prove2me | solution 1 for PI.EF.pTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:29.027055+00:00
-- url     : https://prove2.me/submissions/fb24be93-39e3-4b92-b6be-8e3ef1dddeda

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
import Theorems.Thm_PI_EF_nearB_nonneg
import Theorems.Thm_PI_EF_pTerm_le_far
import Theorems.Thm_PI_EF_pTerm_le_near
import Theorems.Thm_PI_EF_logTerm_nonneg
import Theorems.Thm_PI_EF_log_ge_half


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
theorem _root_.solution {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) (n : ℕ) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n +
      16 * Real.log u * (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
  have hu0 : 0 < u := by linarith
  have hL := log_ge_half hu
  have hA : 0 ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n :=
    mul_nonneg (by positivity) (logTerm_nonneg _ n)
  have hB : 0 ≤ 16 * Real.log u * (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
    apply mul_nonneg (by linarith)
    split_ifs
    · exact nearB_nonneg hu0 hT n
    · exact le_refl _
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · have : pTerm u T n = 0 := by simp [pTerm, h0]
    rw [this]
    linarith
  by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
  · have := pTerm_le_far hu hT hn hfar
    linarith
  · rw [not_or, not_le, not_le] at hfar
    have h := pTerm_le_near hu hT hfar.1 hfar.2
    have f2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have hlt : n < ⌊u⌋₊ + (⌊u⌋₊ + 2) := by
      have : (n : ℝ) < ((⌊u⌋₊ + (⌊u⌋₊ + 2) : ℕ) : ℝ) := by push_cast; linarith [hfar.2]
      exact_mod_cast this
    rw [if_pos hlt]
    linarith
end PI.EF
