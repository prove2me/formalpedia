-- Prove2me | solution 1 for PermanentRollout.FreeAffineInstruction.eval_substituteInputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/41de150e-397f-4fac-a891-3f259335f471

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_FreeAffineForm_eval_substituteInputs

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.FreeAffineInstruction
namespace PermanentRollout.FreeAffineInstruction
theorem _root_.solution {ι κ : Type*}
    (substitution : ι → FreeAffineInput κ)
    (instruction : FreeAffineInstruction ι)
    (values : Array (MvPolynomial ι ℂ)) :
    (instruction.substituteInputs substitution).eval
      (values.map (MvPolynomial.aeval
        (fun index => (substitution index).polynomial))) =
      MvPolynomial.aeval
        (fun index => (substitution index).polynomial)
        (instruction.eval values) := by
  cases instruction with
  | affine form =>
    exact FreeAffineForm.eval_substituteInputs form substitution values
  | mul left right =>
    let φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ :=
      MvPolynomial.aeval (fun index => (substitution index).polynomial)
    have hget (index : ℕ) :
        (values.map φ).getD index 0 = φ (values.getD index 0) := by
      cases hvalue : values[index]? <;> simp [hvalue]
    change
      (values.map φ).getD left 0 * (values.map φ).getD right 0 =
        φ (values.getD left 0 * values.getD right 0)
    rw [map_mul, hget, hget]
end PermanentRollout.FreeAffineInstruction
