-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.vertexCount_eq_leafCount_add_internalGateCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/a394b3fc-4e9e-4bdb-ae47-f32bbb9fad56

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
    vertexCount f = leafCount f + internalGateCount f := by
  induction f <;>
    simp [vertexCount, leafCount, internalGateCount, *, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]
end PermanentFormulaLowerBound.Formula
