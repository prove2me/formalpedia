-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitGate_eq_graphEvaluation_rhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/ba6f5a19-d7dd-4b3f-9286-8d7ea1af6bfd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_circuit_gateEquation
import Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_instructionRhs

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
    freeAffineCircuitGate circuit j =
      freeAffineCircuitGraphEvaluation circuit
        (freeAffineInstructionRhs
          (n := circuit.program.length) (circuit.program.get j)) := by
  rw [freeAffineCircuitGraphEvaluation_instructionRhs]
  exact ReverseAdjoint.circuit_gateEquation circuit j
end PermanentRollout
