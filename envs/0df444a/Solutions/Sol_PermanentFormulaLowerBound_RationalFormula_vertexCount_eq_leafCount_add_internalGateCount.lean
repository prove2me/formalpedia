-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.vertexCount_eq_leafCount_add_internalGateCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/a2b678b9-f2ab-4311-9908-06de20ceaec2

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
theorem _root_.solution
    (f : RationalFormula ι R) :
    vertexCount f = leafCount f + internalGateCount f := by
  induction f <;>
    simp_all [vertexCount, leafCount, internalGateCount, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]
end PermanentFormulaLowerBound.RationalFormula
