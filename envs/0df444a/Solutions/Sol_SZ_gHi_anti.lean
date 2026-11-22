-- Prove2me | solution 1 for SZ.gHi_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:30.654823+00:00
-- url     : https://prove2.me/submissions/c897cc5d-acdf-4d69-862b-ad4664ee5144

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_gHi_succ_lt

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) : Antitone (gHi α) :=
  antitone_nat_of_succ_le fun n => (gHi_succ_lt hα n).le
end SZ
