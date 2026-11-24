-- Prove2me | solution 1 for SchoenfeldBRH.psi_bound_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:12:50.197718+00:00
-- url     : https://prove2.me/submissions/29ae7958-76ad-4219-a223-ef97f2c4f4c0

import Theorems.Thm_SchoenfeldBRH_finitepsi_chunk0
import Theorems.Thm_SchoenfeldBRH_finitepsi_chunk1
import Theorems.Thm_SchoenfeldBRH_finitepsi_chunk2
import Theorems.Thm_SchoenfeldBRH_finitepsi_chunk3

theorem solution :
    ∀ x : ℝ, (73.2 : ℝ) ≤ x → x ≤ Real.exp 13 →
      |Chebyshev.psi x - x| < Real.sqrt x * (Real.log x) ^ 2 / (8 * Real.pi) := by
  intro x hx1 hx2
  have he : Real.exp 13 < 442414 := by
    have h1 : Real.exp 13 = Real.exp 1 ^ 13 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 13 < (2.7182818286 : ℝ) ^ 13 :=
      pow_lt_pow_left₀ h2 (Real.exp_pos 1).le (by norm_num)
    rw [h1]; linarith [show (2.7182818286 : ℝ) ^ 13 < 442414 by norm_num]
  obtain ⟨c0, g0⟩ := SchoenfeldBRH.finitepsi_chunk0
  obtain ⟨c1, g1⟩ := SchoenfeldBRH.finitepsi_chunk1 g0
  obtain ⟨c2, g2⟩ := SchoenfeldBRH.finitepsi_chunk2 g1
  obtain ⟨c3, -⟩ := SchoenfeldBRH.finitepsi_chunk3 g2
  rcases lt_or_ge x 101113 with h | h
  · exact c0 x hx1 h
  rcases lt_or_ge x 214499 with h' | h'
  · exact c1 x h h'
  rcases lt_or_ge x 330047 with h'' | h''
  · exact c2 x h' h''
  · exact c3 x h'' (by linarith)
