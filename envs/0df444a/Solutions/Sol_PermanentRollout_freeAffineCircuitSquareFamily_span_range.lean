-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitSquareFamily_span_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/00d1e97f-5817-4845-9144-6a9faceb67ad

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_ofFn
import Theorems.Thm_PermanentRollout_sourceCircuit_ofList_ofFn_eq_span_range

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
    Ideal.span (Set.range
      (freeAffineCircuitSquareFamily circuit output target)) =
      affineTriangularInstructionIdeal
        (fun j : Fin circuit.program.length =>
          freeAffineInstructionRhs
            (n := circuit.program.length) (circuit.program.get j)) ⊔
      affineGateRawOutputIdeal
        (fun i : Fin k =>
          freeAffineExtendedForm
            (n := circuit.program.length) (output i)) target := by
  rw [← sourceCircuit_ofList_ofFn_eq_span_range,
    freeAffineCircuitSquareFamily_ofFn,
    Ideal.ofList_append,
    sourceCircuit_ofList_ofFn_eq_span_range,
    sourceCircuit_ofList_ofFn_eq_span_range]
  rfl
end PermanentRollout
