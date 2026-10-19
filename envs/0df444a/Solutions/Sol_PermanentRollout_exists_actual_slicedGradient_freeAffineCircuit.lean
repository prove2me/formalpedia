-- Prove2me | solution 1 for PermanentRollout.exists_actual_slicedGradient_freeAffineCircuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/a2ad513b-aeba-41ca-a71c-db001104560b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_FreeAffineForm_eval_substituteInputs
import Theorems.Thm_PermanentRollout_FreeAffineInstruction_eval_substituteInputs
import Theorems.Thm_PermanentRollout_FreeAffineCircuit_values_substituteInputs
import Theorems.Thm_PermanentRollout_ReverseAdjoint_run_inputAdjoints
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_run_multiplicationCount
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_run_inputAdjoints
import Theorems.Thm_PermanentRollout_sourceSlicedGradientLinearInput_polynomial
import Theorems.Thm_PermanentRollout_sourceFreeAffineFormFiniteLinearCombination_eval
import Theorems.Thm_PermanentRollout_sourceSlicedGradientReverseOutputForm_gate_bound

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
    (houtput : output ∈ circuit.outputs)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ)) :
    ∃ D : FreeAffineCircuit (Fin k),
      D.multiplicationCount = 3 * circuit.multiplicationCount ∧
      D.polynomials = (Finset.univ : Finset (Fin k)).toList.map
        (slicedGradientPolynomial (output.eval circuit.values) W A) := by
  classical
  let state := ReverseAdjoint.CircuitAdjoint.run circuit output
  let substitution := sourceSlicedGradientLinearInput W
  let base := state.circuit.substituteInputs substitution
  let forms : List (FreeAffineForm (Fin k)) :=
    (Finset.univ : Finset (Fin k)).toList.map
      (sourceSlicedGradientReverseOutputForm circuit output W A)
  have hvalid : ∀ form ∈ forms, ∀ index : ℕ,
      form.gateCoefficients index ≠ 0 → index < base.program.length := by
    intro form hform index hindex
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hform
    exact sourceSlicedGradientReverseOutputForm_gate_bound
      circuit output W A i index hindex
  refine ⟨base.withOutputs forms hvalid, ?_, ?_⟩
  · change base.multiplicationCount = 3 * circuit.multiplicationCount
    dsimp [base, state, substitution]
    rw [FreeAffineCircuit.multiplicationCount_substituteInputs,
      ReverseAdjoint.CircuitAdjoint.run_multiplicationCount]
  · change forms.map (fun form => form.eval base.values) = _
    dsimp [forms]
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    change (sourceSlicedGradientReverseOutputForm circuit output W A i).eval
      base.values = _
    unfold sourceSlicedGradientReverseOutputForm
    rw [sourceFreeAffineFormFiniteLinearCombination_eval]
    unfold slicedGradientPolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    dsimp [base, state, substitution]
    rw [FreeAffineCircuit.values_substituteInputs,
      FreeAffineForm.eval_substituteInputs,
      ReverseAdjoint.CircuitAdjoint.run_inputAdjoints
        circuit output houtput j]
    congr 1
    apply MvPolynomial.algHom_ext
    intro row
    simpa using sourceSlicedGradientLinearInput_polynomial W row
end PermanentRollout
