-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.affine_gateAdjoints_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/9af25aad-6b7c-4590-9407-63ab6fdb0f53

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
    (form : FreeAffineForm ι) (gate : ℕ) :
    ((state.affine position form).gateAdjoints gate).eval
        (state.affine position form).circuit.values =
      if gate = position then 0 else
        (state.gateAdjoints gate).eval state.circuit.values +
          MvPolynomial.C (form.gateCoefficients gate) *
            (state.gateAdjoints position).eval state.circuit.values := by
  change
    (if gate = position then (0 : FreeAffineForm ι) else
      state.gateAdjoints gate +
        form.gateCoefficients gate • state.gateAdjoints position).eval
          state.circuit.values = _
  split_ifs with hgate
  · simp
  · simp [MvPolynomial.smul_eq_C_mul]
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
