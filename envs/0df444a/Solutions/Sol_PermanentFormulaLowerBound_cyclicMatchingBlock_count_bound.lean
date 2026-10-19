-- Prove2me | solution 1 for PermanentFormulaLowerBound.cyclicMatchingBlock_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/fcf1a745-ec9e-4c13-8c1e-6408731b94a2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingBlock_floor_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (n k : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    n * n ≤ 2 * k * (n * (n / k)) := by
  calc
    n * n ≤ n * (2 * (k * (n / k))) :=
      Nat.mul_le_mul_left n (matchingBlock_floor_bound n k hk hkn)
    _ = 2 * k * (n * (n / k)) := by ring
end PermanentFormulaLowerBound
