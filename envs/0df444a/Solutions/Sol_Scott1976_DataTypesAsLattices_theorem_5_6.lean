-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_5_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:14.593553+00:00
-- url     : https://prove2.me/submissions/53772a24-4c81-4de3-867d-1fa85d9df276

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_16
import Theorems.Thm_Scott1976_DataTypesAsLattices_Vapply_prefixpoint

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a x : Pomega) :
    x ∪ funOf a (Vapply a x) ⊆ Vapply a x := by
  intro k hk
  rcases hk with hk | hk
  · exact eq_5_16 a x hk
  · exact (Vapply_prefixpoint a x).2 hk
end Scott1976.DataTypesAsLattices
