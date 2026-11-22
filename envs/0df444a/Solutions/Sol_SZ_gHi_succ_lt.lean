-- Prove2me | solution 1 for SZ.gHi_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:52.648465+00:00
-- url     : https://prove2.me/submissions/b9da549a-a68f-46e4-9c7e-4effdc58f01a

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_greedy_succ_lt

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) (n : ℕ) : gHi α (n + 1) < gHi α n := by
  have hα0 : (0 : ℝ) < α := by linarith
  rw [gHi, gHi, div_lt_div_iff₀ (pow_pos hα0 (n + 1)) (pow_pos hα0 n)]
  have h := greedy_succ_lt α n
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  calc ((greedy α (n + 1) : ℝ) + 1) * α ^ n
      < (α * (greedy α n : ℝ) + α) * α ^ n :=
        mul_lt_mul_of_pos_right (by linarith) hp
    _ = ((greedy α n : ℝ) + 1) * α ^ (n + 1) := by ring
end SZ
