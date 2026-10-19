-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_fourth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/14bf4088-6aca-4579-83ee-cc74237de971

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_cyclicMatchingBlock_intermediate_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (m : ℕ) (hhalf : n ≤ 2 * m)
    (f : Formula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 4 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    n ^ 4 ≤ 32 * k * variableLeaves f := by
  have hsquare : n * n ≤ 4 * (m * m) := by
    calc
      n * n ≤ (2 * m) * (2 * m) := Nat.mul_self_le_mul_self hhalf
      _ = 4 * (m * m) := by ring
  have hintermediate := cyclicMatchingBlock_intermediate_bound
    hk hkn m f hblock
  calc
    n ^ 4 = (n * n) * (n * n) := by ring
    _ ≤ (n * n) * (4 * (m * m)) :=
      Nat.mul_le_mul_left (n * n) hsquare
    _ = 4 * (n * n * (m * m)) := by ring
    _ ≤ 4 * (8 * k * variableLeaves f) :=
      Nat.mul_le_mul_left 4 hintermediate
    _ = 32 * k * variableLeaves f := by ring
end PermanentFormulaLowerBound.Formula
