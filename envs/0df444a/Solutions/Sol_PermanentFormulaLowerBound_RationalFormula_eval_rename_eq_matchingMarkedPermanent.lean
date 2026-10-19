-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.eval_rename_eq_matchingMarkedPermanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/360c6ed9-6aae-41ff-8c27-1f7c244fc651

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_eval_rename
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_eval_rename

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
variable {ι : Type u} {κ : Type v} {R : Type w}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    eval (rename (matchingVariableEquiv d).symm f) =
      algebraMap
        (MvPolynomial (Y ⊕ matchingOutside d) ℂ)
        (FractionRing (MvPolynomial (Y ⊕ matchingOutside d) ℂ))
        (matchingMarkedPermanent d) := by
  rw [eval_rename, hf, renameFractionEquiv_algebraMap]
  rfl
end PermanentFormulaLowerBound.RationalFormula
