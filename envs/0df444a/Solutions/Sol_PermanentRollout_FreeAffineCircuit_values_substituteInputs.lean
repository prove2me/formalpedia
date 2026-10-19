-- Prove2me | solution 1 for PermanentRollout.FreeAffineCircuit.values_substituteInputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/da2fe7de-bd35-449f-afdd-519b980dccae

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_FreeAffineForm_eval_substituteInputs
import Theorems.Thm_PermanentRollout_FreeAffineInstruction_eval_substituteInputs

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.FreeAffineCircuit
namespace PermanentRollout.FreeAffineCircuit
theorem _root_.solution {ι κ : Type*}
    (circuit : FreeAffineCircuit ι)
    (substitution : ι → FreeAffineInput κ) :
    (circuit.substituteInputs substitution).values =
      circuit.values.map
        (MvPolynomial.aeval
          (fun index => (substitution index).polynomial)) := by
  let φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ :=
    MvPolynomial.aeval (fun index => (substitution index).polynomial)
  have hfold (program : List (FreeAffineInstruction ι))
      (initial : Array (MvPolynomial ι ℂ)) :
      (program.map (FreeAffineInstruction.substituteInputs substitution)).foldl
        (fun current instruction => current.push (instruction.eval current))
        (initial.map φ) =
      (program.foldl
        (fun current instruction => current.push (instruction.eval current))
        initial).map φ := by
    induction program generalizing initial with
    | nil => rfl
    | cons instruction rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [FreeAffineInstruction.eval_substituteInputs,
        ← Array.map_push]
      exact ih (initial.push (instruction.eval initial))
  simpa [values, substituteInputs, φ] using
    hfold circuit.program (#[] : Array (MvPolynomial ι ℂ))
end PermanentRollout.FreeAffineCircuit
