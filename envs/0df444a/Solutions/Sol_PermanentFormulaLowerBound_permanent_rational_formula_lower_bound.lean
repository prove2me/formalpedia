-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanent_rational_formula_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/3efa439c-a0d4-4759-add6-a14edfa764fd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_permanent_size_bounds_of_fourth_power
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_permanent_size_bounds_of_fourth_power
import Theorems.Thm_PermanentFormulaLowerBound_permanent_rational_formula_fourth_power_lower_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (hn : 32 ≤ n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : RationalFormula.Valid f)
    (hf : RationalFormula.eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.variableLeaves f : ℝ) ∧
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.leafCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (192 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.vertexCount f : ℝ) ∧
    (n : ℝ) ^ 4 / (384 * Real.logb 2 (n : ℝ)) ≤
        (RationalFormula.internalGateCount f : ℝ) :=
  RationalFormula.permanent_size_bounds_of_fourth_power hn f
    (permanent_rational_formula_fourth_power_lower_bound hn f hvalid hf)
end PermanentFormulaLowerBound
