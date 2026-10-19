-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.eval_rename_eq_matchingMarkedPermanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/70c121d0-a963-4bc5-992c-c036739f92bc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_eval_rename

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {ι : Type u} {κ : Type v} {R : Type w}
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (f : Formula (Fin n × Fin n) ℂ)
    (hf : eval f = permanentPolynomial n) :
    eval (rename (matchingVariableEquiv d).symm f) =
      matchingMarkedPermanent d := by
  rw [eval_rename, hf]
  rfl
end PermanentFormulaLowerBound.Formula
