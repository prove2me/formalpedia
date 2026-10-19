-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitGraphEvaluation_instructionRhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/d6615b76-e965-4688-8155-393232ca0091

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_reference
import Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_extendedForm

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
    (instruction : FreeAffineInstruction (Fin k)) :
    freeAffineCircuitGraphEvaluation circuit
      (freeAffineInstructionRhs
        (n := circuit.program.length) instruction) =
      instruction.eval circuit.values := by
  cases instruction with
  | affine form =>
      exact freeAffineCircuitGraphEvaluation_extendedForm circuit form
  | mul left right =>
      change
        freeAffineCircuitGraphEvaluation circuit
          (freeAffineGateReference left *
            freeAffineGateReference right) = _
      rw [map_mul,
        freeAffineCircuitGraphEvaluation_reference,
        freeAffineCircuitGraphEvaluation_reference]
      rfl
end PermanentRollout
