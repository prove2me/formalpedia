-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanent_divisionFree_formula_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/23ad77c3-5467-49a8-84f5-7cecf1b50839

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_permanent_size_bounds_of_fourth_power
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_permanent_size_bounds_of_fourth_power
import Theorems.Thm_PermanentFormulaLowerBound_permanent_divisionFree_formula_fourth_power_lower_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (hn : 32 ≤ n)
    (f : Formula (Fin n × Fin n) ℂ)
    (hf : Formula.eval f = permanentPolynomial n) :
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (Formula.variableLeaves f : ℝ) ∧
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (Formula.leafCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (128 * Real.logb 2 (n : ℝ)) ≤
        (Formula.vertexCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (256 * Real.logb 2 (n : ℝ)) ≤
        (Formula.internalGateCount f : ℝ) :=
  Formula.permanent_size_bounds_of_fourth_power hn f
    (permanent_divisionFree_formula_fourth_power_lower_bound hn f hf)
end PermanentFormulaLowerBound
