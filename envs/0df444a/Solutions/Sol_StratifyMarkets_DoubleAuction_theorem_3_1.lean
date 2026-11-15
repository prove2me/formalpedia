-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:45:51.454627+00:00
-- url     : https://prove2.me/submissions/13e14df7-d515-4f4b-aadc-295fecc9b3d7

import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_3_2
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_3_6
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_2_2

set_option autoImplicit false

-- Solutions.Sol_StratifyMarkets_DoubleAuction_theorem_3_1
section
open StratifyMarkets.DoubleAuction

theorem solution (I : BTInstance) :
    ∃ σ : Stratification, 1 / (12 * Real.exp 1) * I.FB ≤ I.strat σ := by
  obtain ⟨M, hm⟩ := lemma_3_6 I
  obtain ⟨σ, hs⟩ := lemma_3_2 I M
  refine ⟨σ, ?_⟩
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  calc
    I.FB ≤ Real.exp 1 * I.roProfit := theorem_2_2 I
    _ ≤ Real.exp 1 * (12 * I.strat σ) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = _ := by ring
end
