-- Prove2me | solution 1 for ShiQMACenteredGap.normalizationRounds_suffice
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T00:10:49.788605+00:00
-- url     : https://prove2.me/submissions/fe697abd-8b59-41ef-850d-1c54a788746d

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_biasIter_dyadic
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Polynomial ℕ) (n : Nat) (hgap : (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (normalizationRounds q n) := by
  have hbudget : q.eval n ≤ 2 ^ rounds q n :=
    (eval_le_pow_budget q n).trans (Nat.pow_le_pow_right (by decide) (by
      dsimp [rounds]; omega))
  have hreal : (↑(q.eval n) : ℝ) ≤ (2 : ℝ) ^ rounds q n := by exact_mod_cast hbudget
  have h := biasIter_dyadic hd hd' (rounds q n)
  rw [min_eq_left (hgap.trans (mul_le_mul_of_nonneg_right hreal hd))] at h
  exact h
