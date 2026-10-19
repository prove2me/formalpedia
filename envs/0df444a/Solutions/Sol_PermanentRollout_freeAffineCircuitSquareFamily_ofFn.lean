-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitSquareFamily_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/62696dd5-6649-428b-a722-f28d8d1bb4ba

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k)) (target : Fin k → ℂ) :
    List.ofFn (freeAffineCircuitSquareFamily circuit output target) =
      (List.ofFn fun j : Fin circuit.program.length =>
        freeAffineCircuitInstructionEquation circuit j) ++
      (List.ofFn fun i : Fin k =>
        freeAffineExtendedForm
          (n := circuit.program.length) (output i) -
          MvPolynomial.C (target i)) := by
  let gates := freeAffineCircuitInstructionEquation circuit
  let outputs : Fin k → MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ :=
    fun i => freeAffineExtendedForm
      (n := circuit.program.length) (output i) - MvPolynomial.C (target i)
  have hcard : circuit.program.length + k =
      Fintype.card (Fin k ⊕ Fin circuit.program.length) := by
    simp [Nat.add_comm]
  have hcast :
      List.ofFn (freeAffineCircuitSquareFamily circuit output target) =
      List.ofFn (Fin.append gates outputs) := by
    simpa [freeAffineCircuitSquareFamily, gates, outputs] using
      (List.ofFn_congr hcard (Fin.append gates outputs)).symm
  rw [hcast, List.ofFn_fin_append]
end PermanentRollout
