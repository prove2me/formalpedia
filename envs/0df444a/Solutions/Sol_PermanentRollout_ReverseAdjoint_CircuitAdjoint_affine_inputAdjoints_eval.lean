-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.affine_inputAdjoints_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/ca0deea7-74e1-46c9-95b0-a7d3310d1117

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
open PermanentRollout.ReverseAdjoint.CircuitAdjoint
namespace PermanentRollout.ReverseAdjoint.CircuitAdjoint
theorem _root_.solution {ι : Type*}
    (state : CircuitAdjoint ι) (position : ℕ)
    (form : FreeAffineForm ι) (input : ι) :
    ((state.affine position form).inputAdjoints input).eval
        (state.affine position form).circuit.values =
      (state.inputAdjoints input).eval state.circuit.values +
        MvPolynomial.C (form.inputCoefficients input) *
          (state.gateAdjoints position).eval state.circuit.values := by
  change
    (state.inputAdjoints input +
      form.inputCoefficients input • state.gateAdjoints position).eval
        state.circuit.values = _
  simp [MvPolynomial.smul_eq_C_mul]
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
