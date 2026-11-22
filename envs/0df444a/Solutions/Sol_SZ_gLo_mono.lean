-- Prove2me | solution 1 for SZ.gLo_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:16.284892+00:00
-- url     : https://prove2.me/submissions/b50d21ac-6a51-40a3-891f-e0a4a4d7ee8c

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_le_greedy_succ

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) : Monotone (gLo α) := by
  have hα0 : (0 : ℝ) < α := by linarith
  refine monotone_nat_of_le_succ fun n => ?_
  rw [gLo, gLo, div_le_div_iff₀ (pow_pos hα0 n) (pow_pos hα0 (n + 1))]
  have h := le_greedy_succ α n
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  calc (greedy α n : ℝ) * α ^ (n + 1) = (α * (greedy α n : ℝ)) * α ^ n := by ring
    _ ≤ (greedy α (n + 1) : ℝ) * α ^ n := mul_le_mul_of_nonneg_right h hp.le
end SZ
