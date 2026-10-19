-- Prove2me | solution 1 for PermanentFormulaLowerBound.two_le_leaves_of_fourth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/52cafe79-7173-43fc-88d7-a08edb160223

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_four_mul_clog_two_lt_self

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n leaves c : ℕ} (hn : 32 ≤ n) (hc : c ≤ 48)
    (hbound : n ^ 4 ≤ c * (2 * Nat.clog 2 n) * leaves) :
    2 ≤ leaves := by
  have hclog : 2 * Nat.clog 2 n ≤ n := by
    have h := four_mul_clog_two_lt_self hn
    omega
  by_contra hleaves
  have hone : leaves ≤ 1 := by omega
  have hsmall : n ^ 4 ≤ 48 * n := by
    calc
      n ^ 4 ≤ c * (2 * Nat.clog 2 n) * leaves := hbound
      _ ≤ c * (2 * Nat.clog 2 n) := by
        simpa using Nat.mul_le_mul_left (c * (2 * Nat.clog 2 n)) hone
      _ ≤ 48 * (2 * Nat.clog 2 n) :=
        Nat.mul_le_mul_right (2 * Nat.clog 2 n) hc
      _ ≤ 48 * n := Nat.mul_le_mul_left 48 hclog
  have hcube : 32 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  have hnpos : 0 < n := by omega
  have hlarge : 48 * n < n ^ 4 := by
    calc
      48 * n < (32 ^ 3) * n :=
        (Nat.mul_lt_mul_right hnpos).2 (by norm_num)
      _ ≤ n ^ 3 * n := Nat.mul_le_mul_right n hcube
      _ = n ^ 4 := by ring
  omega
end PermanentFormulaLowerBound
