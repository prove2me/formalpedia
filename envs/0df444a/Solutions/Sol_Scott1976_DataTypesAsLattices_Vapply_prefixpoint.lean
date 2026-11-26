-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.Vapply_prefixpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:54.81245+00:00
-- url     : https://prove2.me/submissions/7e9cf972-c6d0-403d-a922-b4300aa0d691

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_16
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_right


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a x : Pomega) :
    x ⊆ Vapply a x ∧ funOf a (Vapply a x) ⊆ Vapply a x := by
  refine ⟨eq_5_16 a x, ?_⟩
  intro k hk y hy
  have hV : Vapply a x ⊆ y := fun m hm => hm y hy
  exact hy.2 (funOf_monotone_right a hV hk)
end Scott1976.DataTypesAsLattices
