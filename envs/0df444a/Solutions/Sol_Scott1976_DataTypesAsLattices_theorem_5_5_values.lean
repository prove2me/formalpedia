-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_5_5_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:02.846111+00:00
-- url     : https://prove2.me/submissions/2c50487c-07d7-410c-aad6-5a2785de2f53

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_16
import Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_17

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a x : Pomega) :
    x ⊆ Vapply a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_16 a x, eq_5_17 a x⟩
end Scott1976.DataTypesAsLattices
