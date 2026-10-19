-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitGraphEvaluation_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/51ba3b3f-7c99-47e6-88d8-f0b601c02ef6

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_circuit_values_size

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k)) (r : ℕ) :
    freeAffineCircuitGraphEvaluation circuit
      (freeAffineGateReference
        (k := k) (n := circuit.program.length) r) =
      circuit.values.getD r 0 := by
  classical
  unfold freeAffineGateReference
  split
  next h =>
    simp [freeAffineCircuitGraphEvaluation,
      freeAffineCircuitGate]
  next h =>
    have hsize := ReverseAdjoint.circuit_values_size circuit
    have hout : circuit.values.size ≤ r := by omega
    simp [Array.getD_eq_getD_getElem?, hout]
end PermanentRollout
