-- Prove2me | solution 1 for P2M_SZ_gLo_lt_gHi__a0fcea13b7a8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:07.550635+00:00
-- url     : https://prove2.me/submissions/e5c29c33-aa08-4254-bf7b-28e646cb7383

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_gLo_mono
import Theorems.Thm_SZ_gHi_anti
import Theorems.Thm_SZ_gLo_lt_gHi

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) (n m : ℕ) : gLo α n < gHi α m := by
  rcases le_total n m with h | h
  · exact lt_of_le_of_lt (gLo_mono hα h) (gLo_lt_gHi hα m)
  · exact lt_of_lt_of_le (gLo_lt_gHi hα n) (gHi_anti hα h)
end SZ
