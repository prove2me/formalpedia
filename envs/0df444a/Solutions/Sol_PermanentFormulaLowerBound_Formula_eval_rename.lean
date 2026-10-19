-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.eval_rename
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/97c8f9a9-b107-4c33-aedb-2b2280b6874f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {ι : Type u} {κ : Type v} {R : Type w}
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution [CommRing R] (e : ι ≃ κ) (f : Formula ι R) :
    eval (rename e f) = MvPolynomial.renameEquiv R e (eval f) := by
  induction f with
  | var i => simp [rename, eval, MvPolynomial.renameEquiv_apply]
  | const c => simp [rename, eval, MvPolynomial.renameEquiv_apply]
  | add f g hf hg => simp [rename, eval, hf, hg]
  | sub f g hf hg => simp [rename, eval, hf, hg]
  | mul f g hf hg => simp [rename, eval, hf, hg]
end PermanentFormulaLowerBound.Formula
