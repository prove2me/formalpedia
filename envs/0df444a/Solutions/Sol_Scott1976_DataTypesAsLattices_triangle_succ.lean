-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.triangle_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:26.605116+00:00
-- url     : https://prove2.me/submissions/5223db08-7910-4c3a-ba2b-f8b4b890ee66

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (w : ℕ) : triangle (w + 1) = triangle w + (w + 1) := by
  have hex : (w + 1) * (w + 2) = w * (w + 1) + 2 * (w + 1) := by
    calc
      (w + 1) * (w + 2) = (w + 1) * w + (w + 1) * 2 := Nat.mul_add _ _ _
      _ = w * (w + 1) + 2 * (w + 1) := by
        rw [Nat.mul_comm (w + 1) w, Nat.mul_comm (w + 1) 2]
  simp only [triangle]
  rw [show (w + 1) * ((w + 1) + 1) = (w + 1) * (w + 2) from rfl, hex]
  exact Nat.add_mul_div_left _ _ (by decide : 0 < 2)
end Scott1976.DataTypesAsLattices
