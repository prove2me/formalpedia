-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_5_18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:41.426271+00:00
-- url     : https://prove2.me/submissions/203585dd-195b-4222-b16c-529b47b6054b

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_Icomb_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_retract_app
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x := by
  intro k hk
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have haa : funOf a (funOf a x) ⊆ funOf a x := by
    simp [retract_app ha.2]
  exact hk (funOf a x) ⟨hx, haa⟩
end Scott1976.DataTypesAsLattices
