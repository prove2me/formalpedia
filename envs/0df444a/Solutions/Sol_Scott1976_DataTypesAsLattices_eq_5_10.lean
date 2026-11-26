-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_5_10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:57.862067+00:00
-- url     : https://prove2.me/submissions/1ce15257-70e5-4580-a5f1-1852c245963d

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) : squareSnd (squarePair x y) = y := by
  ext m
  constructor
  · intro hm
    rcases hm with ⟨n, _, h⟩ | ⟨k, hk, h⟩
    · omega
    · have : k = m := by omega
      simpa [this] using hk
  · intro hm
    exact Or.inr ⟨m, hm, rfl⟩
end Scott1976.DataTypesAsLattices
