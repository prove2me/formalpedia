-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.triangle_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:08.834947+00:00
-- url     : https://prove2.me/submissions/3aefc38e-4536-448c-9d55-39c3294c5647

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_succ

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a b : ℕ} (h : a ≤ b) : triangle a ≤ triangle b := by
  induction h with
  | refl => exact le_rfl
  | step h ih =>
    rw [triangle_succ]
    exact le_trans ih (Nat.le_add_right _ _)
end Scott1976.DataTypesAsLattices
