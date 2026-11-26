-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_5_11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:10.415432+00:00
-- url     : https://prove2.me/submissions/6acb9706-1f3c-4163-80f8-39a5ed646545

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_Icomb_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_right


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a b u x : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    funOf u x ⊆ funOf b (funOf u (funOf a x)) := by
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have hy : funOf u (funOf a x) ⊆ funOf b (funOf u (funOf a x)) := by
    have := funOf_monotone_left hb.1 (funOf u (funOf a x))
    rwa [Icomb_app] at this
  exact subset_trans (funOf_monotone_right u hx) hy
end Scott1976.DataTypesAsLattices
