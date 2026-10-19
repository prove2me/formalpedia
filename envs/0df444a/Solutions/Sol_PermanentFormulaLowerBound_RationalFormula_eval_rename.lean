-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.eval_rename
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/e7ac65b4-4982-47c5-8856-523773a5550b

import Mathlib
import Definitions.Def_Permanent

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
    (f : RationalFormula ι R) :
    eval (rename e f) = renameFractionEquiv e (eval f) := by
  induction f with
  | var i =>
      simp [rename, eval, renameFractionEquiv_algebraMap,
        MvPolynomial.renameEquiv_apply]
  | const c =>
      simp [rename, eval, renameFractionEquiv_algebraMap,
        MvPolynomial.renameEquiv_apply]
  | add f g hf hg => simp [rename, eval, hf, hg]
  | sub f g hf hg => simp [rename, eval, hf, hg]
  | mul f g hf hg => simp [rename, eval, hf, hg]
  | div f g hf hg => simp [rename, eval, hf, hg, map_div₀]
end PermanentFormulaLowerBound.RationalFormula
