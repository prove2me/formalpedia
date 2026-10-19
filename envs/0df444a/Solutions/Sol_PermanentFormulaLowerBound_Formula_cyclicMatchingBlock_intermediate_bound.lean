-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_intermediate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/73d0dcff-75e0-4c95-901a-0e56b3f3b623

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_cyclicMatchingBlock_count_bound
import Theorems.Thm_PermanentFormulaLowerBound_Formula_cyclicMatchingBlock_square_sum_le_variableLeaves

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
    (m : ℕ) (f : Formula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 4 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    n * n * (m * m) ≤ 8 * k * variableLeaves f := by
  have hcount := cyclicMatchingBlock_count_bound n k hk hkn
  have hsum := cyclicMatchingBlock_square_sum_le_variableLeaves
    hk m f hblock
  calc
    n * n * (m * m) ≤
        (2 * k * (n * (n / k))) * (m * m) :=
          Nat.mul_le_mul_right (m * m) hcount
    _ = 2 * k * ((n * (n / k)) * (m * m)) := by ring
    _ ≤ 2 * k * (4 * variableLeaves f) :=
      Nat.mul_le_mul_left (2 * k) hsum
    _ = 8 * k * variableLeaves f := by ring
end PermanentFormulaLowerBound.Formula
