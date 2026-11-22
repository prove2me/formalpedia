-- Prove2me | solution 1 for SZ.gLo_le_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:29.071881+00:00
-- url     : https://prove2.me/submissions/0dd1f3d1-e2f1-40a9-a3af-d52d64031f42

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_gLo_bddAbove

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) (n : ℕ) : gLo α n ≤ tijdemanWitness α :=
  le_ciSup (gLo_bddAbove hα) n
end SZ
