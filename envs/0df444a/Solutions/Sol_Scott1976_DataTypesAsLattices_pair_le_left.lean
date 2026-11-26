-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.pair_le_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:25.716741+00:00
-- url     : https://prove2.me/submissions/29db9877-7842-448d-9139-fd40c1e5d5cb

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (n m : ℕ) : n ≤ pair n m := by
  have htri : n ≤ triangle (n + m) := by
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      have hmul : n.succ * 2 ≤ (n.succ + m) * (n.succ + m + 1) :=
        Nat.mul_le_mul
          (Nat.le_add_right n.succ m)
          (Nat.succ_le_succ
            (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_add_right n.succ m)))
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hmul
  exact htri.trans (Nat.le_add_right _ _)
end Scott1976.DataTypesAsLattices
