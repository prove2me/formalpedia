-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitInstructionEquation_totalDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/6966cfa1-61b6-4e8a-8dc8-460557c3433f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_multiplication_gate_equation_totalDegree_le_two
import Theorems.Thm_PermanentRollout_freeAffineGateReference_totalDegree_le_one
import Theorems.Thm_PermanentRollout_freeAffineExtendedForm_totalDegree_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (j : Fin circuit.program.length) :
    (freeAffineCircuitInstructionEquation circuit j).totalDegree ≤
      if (circuit.program.get j).isMultiplication then 2 else 1 := by
  classical
  unfold freeAffineCircuitInstructionEquation
  generalize heq : circuit.program.get j = instruction
  cases instruction with
  | affine form =>
      simp only [FreeAffineInstruction.isMultiplication,
        Bool.false_eq_true, ↓reduceIte]
      exact (MvPolynomial.totalDegree_sub _ _).trans
        (max_le (by simp)
          (freeAffineExtendedForm_totalDegree_le_one form))
  | mul left right =>
      simp only [FreeAffineInstruction.isMultiplication,
        ↓reduceIte]
      exact multiplication_gate_equation_totalDegree_le_two
        (Sum.inr j)
        (freeAffineGateReference left)
        (freeAffineGateReference right)
        (freeAffineGateReference_totalDegree_le_one left)
        (freeAffineGateReference_totalDegree_le_one right)
end PermanentRollout
