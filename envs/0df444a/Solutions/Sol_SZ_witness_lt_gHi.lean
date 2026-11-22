-- Prove2me | solution 1 for SZ.witness_lt_gHi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:57.150124+00:00
-- url     : https://prove2.me/submissions/d6334f10-80a9-47e4-92a9-725ad69a9fbc

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_gHi_succ_lt
import Theorems.Thm_P2M_SZ_gLo_lt_gHi__a0fcea13b7a8

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) (n : ℕ) : tijdemanWitness α < gHi α n :=
  lt_of_le_of_lt (ciSup_le fun k => (gLo_lt_gHi' hα k (n + 1)).le) (gHi_succ_lt hα n)
end SZ
