-- Prove2me | solution 1 for RareDisease.ExogOutcome.best_response
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:32:21.495195+00:00
-- url     : https://prove2.me/submissions/5f55c7f2-11ec-4702-a614-973b8ecf1225

import Mathlib
import Definitions.Def_RareDisease_ExogOutcome_Setting
open RareDisease.ExogOutcome

theorem solution(k p α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hpol : RareDisease.Endogenous.IsPolicy α β) :
    BR k p α β = {p * (1 - (1 - β) * p) / (2 * (1 - α) * k)} := by
  obtain ⟨⟨hα0, hα1⟩, ⟨hβ0, hβ1⟩⟩ := hpol
  have hc : 0 < (1 - α) * k := mul_pos (by linarith) hk
  have hA : 0 < p * (1 - (1 - β) * p) := by
    apply mul_pos hp0
    nlinarith [mul_le_mul_of_nonneg_right (show 1 - β ≤ 1 by linarith) hp0.le]
  have hden : (2 * (1 - α) * k) ≠ 0 := by nlinarith
  have key : ∀ e : ℝ, profit k p α β (p * (1 - (1 - β) * p) / (2 * (1 - α) * k)) - profit k p α β e
      = (1 - α) * k * (e - p * (1 - (1 - β) * p) / (2 * (1 - α) * k)) ^ 2 := by
    intro e
    unfold profit
    field_simp
    ring
  ext e
  simp only [BR, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨he, hmax⟩
    have h1 := hmax (p * (1 - (1 - β) * p) / (2 * (1 - α) * k)) (div_pos hA (by linarith))
    have h2 := key e
    have h3 : (1 - α) * k * (e - p * (1 - (1 - β) * p) / (2 * (1 - α) * k)) ^ 2 ≤ 0 := by linarith
    have h4 : (e - p * (1 - (1 - β) * p) / (2 * (1 - α) * k)) ^ 2 = 0 := by
      have := sq_nonneg (e - p * (1 - (1 - β) * p) / (2 * (1 - α) * k))
      have h5 : (e - p * (1 - (1 - β) * p) / (2 * (1 - α) * k)) ^ 2 ≤ 0 := by
        by_contra hh
        push_neg at hh
        nlinarith [mul_pos hc hh]
      linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4
    linarith
  · intro he
    rw [he]
    refine ⟨div_pos hA (by linarith), fun e' _ => ?_⟩
    have := key e'
    nlinarith [mul_nonneg hc.le (sq_nonneg (e' - p * (1 - (1 - β) * p) / (2 * (1 - α) * k)))]
