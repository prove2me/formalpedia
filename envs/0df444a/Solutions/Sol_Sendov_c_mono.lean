-- Prove2me | solution 1 for Sendov.c_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:51:23.149082+00:00
-- url     : https://prove2.me/submissions/55b7cf97-a97e-4383-b56d-8aa596188a28

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : c m α ≤ c n α := by
  have hMm : 0 < M m := M_pos hm
  have hMle : M m ≤ M n := by
    simp only [M]
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  have : α / M n ≤ α / M m := div_le_div_of_nonneg_left hα hMm hMle
  simp only [c]
  linarith
end Sendov
