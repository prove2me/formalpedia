-- Prove2me | solution 1 for SZ.le_greedy_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:48:33.55866+00:00
-- url     : https://prove2.me/submissions/9937b5b8-fe7c-4283-80de-2e6a9bacac39

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_greedy_succ

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (α : ℝ) (n : ℕ) :
    α * (greedy α n : ℝ) ≤ (greedy α (n + 1) : ℝ) := by
  have h := Int.le_ceil (α * (greedy α n : ℝ) / 2)
  rw [greedy_succ]; push_cast; linarith
end SZ
