-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanent_divisionFree_formula_logarithmic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/9e35ff83-d121-4844-a913-469a20c051c4

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_permanent_divisionFree_formula_lower_bound

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
      (Formula.variableLeaves f : ℝ) :=
  (permanent_divisionFree_formula_lower_bound hn f hf).1
end PermanentFormulaLowerBound
