-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.valid_rename
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/9824cd7e-a4d7-4355-9f34-b8ffb414db40

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
theorem _root_.solution [Field R] (e : ι ≃ κ)
    {f : RationalFormula ι R} (h : Valid f) :
    Valid (rename e f) := by
  induction h with
  | var i => exact .var _
  | const c => exact .const _
  | add hf hg ihf ihg => exact .add ihf ihg
  | sub hf hg ihf ihg => exact .sub ihf ihg
  | mul hf hg ihf ihg => exact .mul ihf ihg
  | div hf hg hden ihf ihg =>
      apply Valid.div ihf ihg
      intro hzero
      apply hden
      apply (renameFractionEquiv e).injective
      simpa [eval_rename] using hzero
end PermanentFormulaLowerBound.RationalFormula
