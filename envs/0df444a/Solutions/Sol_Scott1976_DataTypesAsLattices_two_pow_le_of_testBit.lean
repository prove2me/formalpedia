-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.two_pow_le_of_testBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:03.735082+00:00
-- url     : https://prove2.me/submissions/7e413887-8c27-491d-b20f-55ba3c716448

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
theorem _root_.solution {n k : ℕ} (h : n.testBit k) : 2 ^ k ≤ n := by
  have hmod : (n >>> k) % 2 = 1 := by simpa [Nat.testBit] using h
  have hpos : 0 < n >>> k := Nat.pos_of_ne_zero fun hz => by simp [hz] at hmod
  have hdiv : 1 ≤ n / 2 ^ k := by
    rwa [Nat.shiftRight_eq_div_pow] at hpos
  simpa using (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mp hdiv
end Scott1976.DataTypesAsLattices
