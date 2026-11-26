-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_5_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:49.176274+00:00
-- url     : https://prove2.me/submissions/849eb5f9-33e8-4dda-b28c-6bdec7bd6376

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_ii


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u : Pomega) : u ⊆ graph (fun x => funOf u x) :=
  theorem_1_2_ii u
end Scott1976.DataTypesAsLattices
