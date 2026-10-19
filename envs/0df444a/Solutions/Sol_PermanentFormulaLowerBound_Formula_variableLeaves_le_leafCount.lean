-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.variableLeaves_le_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/b5708359-701e-48f7-8578-39bd3e7ae2c5

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {ι : Type u} {R : Type v}
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution (f : Formula ι R) :
    variableLeaves f ≤ leafCount f := by
  induction f with
  | var i => simp [variableLeaves, leafCount]
  | const c => simp [variableLeaves, leafCount]
  | add f g hf hg =>
      simpa [variableLeaves, leafCount] using Nat.add_le_add hf hg
  | sub f g hf hg =>
      simpa [variableLeaves, leafCount] using Nat.add_le_add hf hg
  | mul f g hf hg =>
      simpa [variableLeaves, leafCount] using Nat.add_le_add hf hg
end PermanentFormulaLowerBound.Formula
