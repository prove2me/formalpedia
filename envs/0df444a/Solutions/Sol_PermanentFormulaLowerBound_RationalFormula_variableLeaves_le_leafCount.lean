-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.variableLeaves_le_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/c528fb12-4785-47f6-a9db-50c8b65d21bd

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
variable {ι : Type u} {R : Type v}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution (f : RationalFormula ι R) :
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
  | div f g hf hg =>
      simpa [variableLeaves, leafCount] using Nat.add_le_add hf hg
end PermanentFormulaLowerBound.RationalFormula
