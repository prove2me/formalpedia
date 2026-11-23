-- Prove2me | solution 1 for StrongWeakEq.TwoState.display_4_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:19:43.992376+00:00
-- url     : https://prove2.me/submissions/7975e1d3-300d-423d-869e-d3a81806bfa2

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel
import Definitions.Def_StrongWeakEq_TwoState_Example43
import Theorems.Thm_StrongWeakEq_TwoState_display_4_3
import Theorems.Thm_StrongWeakEq_TwoState_display_4_5

set_option autoImplicit false

open StrongWeakEq.TwoState

theorem StrongWeakEq.TwoState.ex43_Lambda_formula (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) (7 / 12)) :
    StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 (gen (5 / 12) b) =
      -(1 / 12) * b - 579 / 288 := by
  have hlam : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := ⟨by norm_num, by norm_num⟩
  have h45 := (display_4_5 (1 / 2) 1 2 hlam (by norm_num) (by norm_num) ex43g₁ ex43g₂ (5 / 12) b
    (5 / 12) (7 / 12) (by norm_num) hb.1 (by norm_num) (by norm_num)).2.2
  have h43 := display_4_3 (1 / 2) 1 2 hlam (by norm_num) (by norm_num) ex43g₁ ex43g₂ (5 / 12) (7 / 12)
    (by norm_num) (by norm_num)
  show StrongWeakEq.Existence.Lambda (twoStatePayoff (1 / 2) 1 2 ex43g₁ ex43g₂)
    (twoStatePayoffDeriv (1 / 2) 1 2 ex43g₁ ex43g₂) (gen (5 / 12) (7 / 12)) 1 (gen (5 / 12) b) = _
  rw [h45, h43.1, h43.2]
  have hg1 : ex43g₁ (5 / 12) = -(25 / 144) := by unfold ex43g₁; norm_num
  have hg2s : ex43g₂ (7 / 12) = 263 / 144 := by
    unfold ex43g₂
    rw [if_neg (by norm_num)]
    norm_num
  have hg2b : ex43g₂ b = 193 / 144 + 5 / 6 * b := by
    unfold ex43g₂
    split_ifs with h
    · rfl
    · have : b = 7 / 12 := le_antisymm hb.2 (not_lt.mp h)
      subst this
      norm_num
  rw [hg1, hg2s, hg2b]
  ring

theorem solution :
    (∀ b ∈ Set.Icc (0:ℝ) (7 / 12),
      StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 (gen (5 / 12) b) = -(1 / 12) * b - 579 / 288) ∧
    (∀ b ∈ Set.Ico (0:ℝ) (7 / 12),
      StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 Qstar < StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 (gen (5 / 12) b)) := by
  refine ⟨StrongWeakEq.TwoState.ex43_Lambda_formula, ?_⟩
  intro b hb
  have h1 := StrongWeakEq.TwoState.ex43_Lambda_formula b ⟨hb.1, hb.2.le⟩
  have h2 := StrongWeakEq.TwoState.ex43_Lambda_formula (7 / 12) ⟨by norm_num, le_rfl⟩
  have h2' : StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 Qstar =
      -(1 / 12) * (7 / 12) - 579 / 288 := h2
  rw [h2', h1]
  linarith [hb.2]
