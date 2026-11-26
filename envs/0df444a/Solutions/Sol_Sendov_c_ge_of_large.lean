-- Prove2me | solution 1 for Sendov.c_ge_of_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:52.482119+00:00
-- url     : https://prove2.me/submissions/bac8654e-5caa-4e7e-bc0d-b8d7031621bc

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : 81 / 200 ≤ c n α := by
  have hM : (100 : ℝ) ≤ M n := by
    have : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [M]; linarith
  have hM0 : (0 : ℝ) < M n := by linarith
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : α / M n ≤ 17 / 100 := by
    rw [div_le_iff₀ hM0]
    nlinarith
  have h2 : α / (2 * (3 + α)) ≤ 17 / 40 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (3 + α))]
    nlinarith
  linarith
end Sendov
