-- Prove2me | solution 1 for SZ.greedy_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:04.909237+00:00
-- url     : https://prove2.me/submissions/91d37e2a-32ad-49a8-8da7-f04b240bc7f7

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_greedy_zero
import Theorems.Thm_SZ_greedy_succ
attribute [local simp] SZ.greedy_zero

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (α : ℝ) (n : ℕ) : Even (greedy α n) := by
  cases n with
  | zero => exact ⟨1, by norm_num [greedy_zero]⟩
  | succ n => exact ⟨⌈α * (greedy α n : ℝ) / 2⌉, by rw [greedy_succ]; ring⟩
end SZ
