-- Prove2me | solution 1 for SZ.greedy_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:14.235384+00:00
-- url     : https://prove2.me/submissions/32cbd990-8a68-4c93-9fd7-e59673cf036c

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
    (greedy α (n + 1) : ℝ) < α * (greedy α n : ℝ) + 2 := by
  have h := Int.ceil_lt_add_one (α * (greedy α n : ℝ) / 2)
  rw [greedy_succ]; push_cast; linarith
end SZ
