-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:22.724+00:00
-- url     : https://prove2.me/submissions/0e1bb983-73f0-4468-b754-58b3f22fd26c

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_17
import Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_18

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_18 ha x, eq_5_17 a x⟩
end Scott1976.DataTypesAsLattices
