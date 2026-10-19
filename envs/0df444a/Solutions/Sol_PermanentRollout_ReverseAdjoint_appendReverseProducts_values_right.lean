-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.appendReverseProducts_values_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/9b09d90e-8bf1-4975-a233-21e7084a3e20

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_circuit_values_size
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_values

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (circuit : FreeAffineCircuit ι) (adjoint : FreeAffineForm ι)
    (left right : ℕ)
    (hadjoint : ∀ index, adjoint.gateCoefficients index ≠ 0 →
      index < circuit.program.length)
    (hleft : left < circuit.program.length)
    (hright : right < circuit.program.length) :
    (appendReverseProducts circuit adjoint left right
      hadjoint hleft hright).values.getD
        (circuit.program.length + 1) 0 =
          adjoint.eval circuit.values * circuit.values.getD right 0 := by
  rw [appendReverseProducts_values, ← circuit_values_size circuit]
  have hmiddle : circuit.values.size + 1 <
      ((circuit.values.push (adjoint.eval circuit.values)).push
        (adjoint.eval circuit.values *
          circuit.values.getD right 0)).size := by
    simp
  have hlast : circuit.values.size + 1 <
      (((circuit.values.push (adjoint.eval circuit.values)).push
        (adjoint.eval circuit.values *
          circuit.values.getD right 0)).push
            (adjoint.eval circuit.values *
              circuit.values.getD left 0)).size := by
    simp
  calc
    (((circuit.values.push (adjoint.eval circuit.values)).push
        (adjoint.eval circuit.values *
          circuit.values.getD right 0)).push
            (adjoint.eval circuit.values *
              circuit.values.getD left 0)).getD
                (circuit.values.size + 1) 0 =
      (((circuit.values.push (adjoint.eval circuit.values)).push
        (adjoint.eval circuit.values *
          circuit.values.getD right 0)).push
            (adjoint.eval circuit.values *
              circuit.values.getD left 0))[circuit.values.size + 1]'hlast :=
                  (Array.getElem_eq_getD 0).symm
    _ = ((circuit.values.push (adjoint.eval circuit.values)).push
          (adjoint.eval circuit.values *
            circuit.values.getD right 0))[circuit.values.size + 1]'hmiddle :=
                Array.getElem_push_lt hmiddle
    _ = adjoint.eval circuit.values * circuit.values.getD right 0 := by
      simpa using
        (Array.getElem_push_eq
          (xs := circuit.values.push (adjoint.eval circuit.values))
          (x := adjoint.eval circuit.values *
            circuit.values.getD right 0))
end PermanentRollout.ReverseAdjoint
