-- Prove2me | solution 1 for PermanentRollout.sourceSlicedGradientReverseOutputForm_gate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/7192bd02-fb8e-466f-9933-6fb483a9d123

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceFreeAffineFormFiniteLinearCombination_gate_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k m : ℕ}
    (circuit : FreeAffineCircuit (Fin m))
    (output : FreeAffineForm (Fin m))
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (i : Fin k) (index : ℕ)
    (hindex : (sourceSlicedGradientReverseOutputForm
      circuit output W A i).gateCoefficients index ≠ 0) :
    index <
      ((ReverseAdjoint.CircuitAdjoint.run circuit output).circuit.substituteInputs
        (sourceSlicedGradientLinearInput W)).program.length := by
  apply sourceFreeAffineFormFiniteLinearCombination_gate_bound
    (fun j : Fin m => (A (Pi.single j 1)) i)
    (fun j : Fin m =>
      (((ReverseAdjoint.CircuitAdjoint.run circuit output).inputAdjoints j).substituteInputs
        (sourceSlicedGradientLinearInput W)))
    ((ReverseAdjoint.CircuitAdjoint.run circuit output).circuit.substituteInputs
      (sourceSlicedGradientLinearInput W)).program.length
    ?_ index hindex
  intro j r hr
  have h := (ReverseAdjoint.CircuitAdjoint.run circuit output).validInputAdjoints j r
    (by simpa [FreeAffineForm.substituteInputs] using hr)
  simpa [FreeAffineCircuit.substituteInputs] using h
end PermanentRollout
