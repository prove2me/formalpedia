-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_5_17
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:00.786607+00:00
-- url     : https://prove2.me/submissions/7c513374-31c4-43de-b411-2e59cbaee84c

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_16

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a x : Pomega) : Vapply a (Vapply a x) = Vapply a x := by
  apply subset_antisymm
  · intro k hk y hy
    have : Vapply a x ⊆ y := by
      intro m hm
      exact hm y hy
    exact hk y ⟨this, hy.2⟩
  · exact eq_5_16 a (Vapply a x)
end Scott1976.DataTypesAsLattices
