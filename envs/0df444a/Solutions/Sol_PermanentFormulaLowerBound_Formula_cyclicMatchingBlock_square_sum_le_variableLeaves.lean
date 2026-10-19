-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_square_sum_le_variableLeaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/60e7c764-b7a5-45c1-a1a7-271adfaf8a65

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_cyclicMatchingBlock_disjoint
import Theorems.Thm_PermanentFormulaLowerBound_Formula_sum_blockLeaves_le_variableLeaves_of_disjoint
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_sum_blockLeaves_le_variableLeaves_of_disjoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {n k : ℕ} (hk : 0 < k) (m : ℕ)
    (f : Formula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 4 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    (n * (n / k)) * (m * m) ≤ 4 * variableLeaves f := by
  classical
  have hpack := sum_blockLeaves_le_variableLeaves_of_disjoint
    (fun x : Fin n × Fin (n / k) => cyclicMatchingBlock hk x.1 x.2)
    (fun a b hab => cyclicMatchingBlock_disjoint hk a b hab) f
  calc
    (n * (n / k)) * (m * m) =
        ∑ _x : Fin n × Fin (n / k), m * m := by
          simp
    _ ≤ ∑ x : Fin n × Fin (n / k),
          4 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f := by
            exact Finset.sum_le_sum fun x _ => hblock x
    _ = 4 * ∑ x : Fin n × Fin (n / k),
          blockLeaves (cyclicMatchingBlock hk x.1 x.2) f := by
            rw [Finset.mul_sum]
    _ ≤ 4 * variableLeaves f := Nat.mul_le_mul_left 4 hpack
end PermanentFormulaLowerBound.Formula
