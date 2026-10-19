-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBlock_floor_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/c00c1837-5f8c-4c90-ba65-263c942a0d54

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (n k : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    n ≤ 2 * (k * (n / k)) := by
  have hq : 0 < n / k := Nat.div_pos hkn hk
  have hkq : k ≤ k * (n / k) := by
    simpa using Nat.mul_le_mul_left k (Nat.succ_le_of_lt hq)
  have hrem : n % k < k := Nat.mod_lt n hk
  have hdecomp : n % k + k * (n / k) = n := Nat.mod_add_div n k
  omega
end PermanentFormulaLowerBound
