-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:52.576167+00:00
-- url     : https://prove2.me/submissions/62d82b5c-c015-42be-97c3-e0bcd03cd43f

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_pair_eq_triangle
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_succ
import Theorems.Thm_Scott1976_DataTypesAsLattices_exists_triangle_bucket
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (k : ℕ) : ∃ n m, pair n m = k := by
  obtain ⟨w, hle, hlt⟩ := exists_triangle_bucket k
  refine ⟨w - (k - triangle w), k - triangle w, ?_⟩
  have hm : k - triangle w ≤ w := by
    have : k < triangle w + (w + 1) := by rwa [triangle_succ] at hlt
    omega
  have : w - (k - triangle w) + (k - triangle w) = w := Nat.sub_add_cancel hm
  simp [pair_eq_triangle, this, Nat.add_sub_of_le hle]
end Scott1976.DataTypesAsLattices
