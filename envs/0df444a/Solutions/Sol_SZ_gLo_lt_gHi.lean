-- Prove2me | solution 1 for SZ.gLo_lt_gHi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:17.197721+00:00
-- url     : https://prove2.me/submissions/24bfa29a-893f-495f-858a-601d42ea1b7a

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) (n : ℕ) : gLo α n < gHi α n := by
  have hα0 : (0 : ℝ) < α := by linarith
  rw [gLo, gHi, div_lt_div_iff₀ (pow_pos hα0 n) (pow_pos hα0 n)]
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  nlinarith
end SZ
