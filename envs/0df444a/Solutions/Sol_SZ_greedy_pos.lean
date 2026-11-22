-- Prove2me | solution 1 for SZ.greedy_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:26.680557+00:00
-- url     : https://prove2.me/submissions/d67143d8-34a3-4450-90b9-7883d263d25b

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_greedy_zero
import Theorems.Thm_SZ_le_greedy_succ
attribute [local simp] SZ.greedy_zero

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) (n : ℕ) : 0 < (greedy α n : ℝ) := by
  induction n with
  | zero => norm_num [greedy_zero]
  | succ n ih =>
    have := le_greedy_succ α n
    nlinarith
end SZ
