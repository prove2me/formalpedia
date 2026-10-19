-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.permanent_size_bounds_of_fourth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/557ee6a3-1927-4504-834d-7a54a8ae7c1c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_leafCount_eq_internalGateCount_add_one
import Theorems.Thm_PermanentFormulaLowerBound_Formula_leafCount_le_vertexCount
import Theorems.Thm_PermanentFormulaLowerBound_Formula_variableLeaves_le_leafCount
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_leafCount_eq_internalGateCount_add_one
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_variableLeaves_le_leafCount
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_leafCount_le_vertexCount
import Theorems.Thm_PermanentFormulaLowerBound_divisionFree_logarithmic_lower_bound
import Theorems.Thm_PermanentFormulaLowerBound_divisionFree_internal_logarithmic_lower_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {n : ℕ} (hn : 32 ≤ n)
    (f : Formula (Fin n × Fin n) ℂ)
    (hfour : n ^ 4 ≤
      32 * (2 * Nat.clog 2 n) * variableLeaves f) :
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (variableLeaves f : ℝ) ∧
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (leafCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (vertexCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (256 * Real.logb 2 (n : ℝ)) ≤
        (internalGateCount f : ℝ) := by
  have hleaf : n ^ 4 ≤ 32 * (2 * Nat.clog 2 n) * leafCount f :=
    hfour.trans
      (Nat.mul_le_mul_left (32 * (2 * Nat.clog 2 n))
        (variableLeaves_le_leafCount f))
  have hvertex : n ^ 4 ≤ 32 * (2 * Nat.clog 2 n) * vertexCount f :=
    hfour.trans
      (Nat.mul_le_mul_left (32 * (2 * Nat.clog 2 n))
        ((variableLeaves_le_leafCount f).trans
          (leafCount_le_vertexCount f)))
  exact
    ⟨divisionFree_logarithmic_lower_bound hn hfour,
      divisionFree_logarithmic_lower_bound hn hleaf,
      divisionFree_logarithmic_lower_bound hn hvertex,
      divisionFree_internal_logarithmic_lower_bound hn
        (leafCount_eq_internalGateCount_add_one f) hleaf⟩
end PermanentFormulaLowerBound.Formula
