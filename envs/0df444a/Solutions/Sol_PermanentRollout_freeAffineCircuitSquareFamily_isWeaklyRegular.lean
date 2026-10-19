-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitSquareFamily_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/0d5459ef-39af-4e72-b390-7122ad259e6f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_translated_isWeaklyRegular
import Theorems.Thm_PermanentRollout_affine_triangular_instruction_output_equations_isWeaklyRegular
import Theorems.Thm_PermanentRollout_freeAffineInstructionRhs_mem_gate_vars
import Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_extendedForm
import Theorems.Thm_PermanentRollout_freeAffineCircuitGate_eq_graphEvaluation_rhs
import Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_ofFn

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k))
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : Fin k → ℂ)
    (houtput : ∀ i, (output i).eval circuit.values = F i) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k ⊕ Fin circuit.program.length) ℂ)
      (List.ofFn (freeAffineCircuitSquareFamily circuit output target)) := by
  rw [freeAffineCircuitSquareFamily_ofFn]
  apply affine_triangular_instruction_output_equations_isWeaklyRegular
    (fun j : Fin circuit.program.length =>
      freeAffineInstructionRhs
        (n := circuit.program.length) (circuit.program.get j))
    (freeAffineCircuitGate circuit)
    (fun i : Fin k =>
      freeAffineExtendedForm
        (n := circuit.program.length) (output i))
    F target
  · intro j
    simpa [affineGateGraphEvaluation,
      freeAffineCircuitGraphEvaluation] using
      freeAffineCircuitGate_eq_graphEvaluation_rhs circuit j
  · intro j i hi
    exact freeAffineInstructionRhs_mem_gate_vars
      (circuit.program.get j) j (circuit.valid j) i hi
  · intro i
    simpa [affineGateGraphEvaluation,
      freeAffineCircuitGraphEvaluation] using
      (freeAffineCircuitGraphEvaluation_extendedForm
        circuit (output i)).trans (houtput i)
  · exact homogeneousMap_allTarget_translated_isWeaklyRegular
      F target e he hF hzero
end PermanentRollout
