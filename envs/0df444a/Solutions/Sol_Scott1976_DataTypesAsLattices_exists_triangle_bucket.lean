-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.exists_triangle_bucket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:28.856224+00:00
-- url     : https://prove2.me/submissions/cb6c9e71-5076-4d9e-844d-0cdad7438c09

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_succ
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (k : ℕ) :
    ∃ w, triangle w ≤ k ∧ k < triangle (w + 1) := by
  let P := fun w : ℕ => k < triangle (w + 1)
  have hP : ∃ w, P w := ⟨k, by
    change k < triangle (k + 1)
    rw [triangle_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) _)⟩
  let w := Nat.find hP
  refine ⟨w, ?_, Nat.find_spec hP⟩
  cases hw : w with
  | zero => simp [triangle]
  | succ w' =>
    have hmin : ¬ P w' :=
      Nat.find_min hP (Nat.lt_of_succ_le (by
        have : w = Nat.find hP := rfl
        rw [← this, hw]))
    exact Nat.le_of_not_gt hmin
end Scott1976.DataTypesAsLattices
