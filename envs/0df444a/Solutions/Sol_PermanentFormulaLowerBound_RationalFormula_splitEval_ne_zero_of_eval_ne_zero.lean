-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.splitEval_ne_zero_of_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/af66bb03-7049-4d5b-bee7-dc0c91b576d1

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_splitFractionHom_injective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
noncomputable section
variable {Y Z F : Type*}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution [Field F]
    {f : RationalFormula (Y ⊕ Z) F} (h : eval f ≠ 0) :
    splitEval f ≠ 0 := by
  intro hzero
  apply h
  apply splitFractionHom_injective (Y := Y) (Z := Z) (F := F)
  simpa [splitEval] using hzero
end PermanentFormulaLowerBound.RationalFormula
