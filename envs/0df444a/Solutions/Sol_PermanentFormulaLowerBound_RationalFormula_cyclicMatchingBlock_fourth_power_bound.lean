-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.cyclicMatchingBlock_fourth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/71deaaca-f9ea-4646-be27-65186653435b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_cyclicMatchingBlock_intermediate_bound
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_cyclicMatchingBlock_intermediate_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (m : ℕ) (hhalf : n ≤ 2 * m)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 6 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    n ^ 4 ≤ 48 * k * variableLeaves f := by
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
    _ ≤ 4 * (12 * k * variableLeaves f) :=
      Nat.mul_le_mul_left 4 hintermediate
    _ = 48 * k * variableLeaves f := by ring
end PermanentFormulaLowerBound.RationalFormula
