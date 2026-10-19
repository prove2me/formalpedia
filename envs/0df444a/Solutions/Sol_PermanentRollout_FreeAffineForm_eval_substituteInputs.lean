-- Prove2me | solution 1 for PermanentRollout.FreeAffineForm.eval_substituteInputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/4fe4175e-826f-4c79-bdf5-dcf7876ed375

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.FreeAffineForm
namespace PermanentRollout.FreeAffineForm
theorem _root_.solution {ι κ : Type*} (form : FreeAffineForm ι)
    (substitution : ι → FreeAffineInput κ)
    (values : Array (MvPolynomial ι ℂ)) :
    (form.substituteInputs substitution).eval
      (values.map (MvPolynomial.aeval
        (fun index => (substitution index).polynomial))) =
      MvPolynomial.aeval
        (fun index => (substitution index).polynomial)
        (form.eval values) := by
  let φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ :=
    MvPolynomial.aeval (fun index => (substitution index).polynomial)
  have hgate (index : ℕ) :
      (values.map φ).getD index 0 = φ (values.getD index 0) := by
    cases hvalue : values[index]? <;> simp [hvalue]
  have hgateCombination :
      Finsupp.linearCombination ℂ
        (fun index => (values.map φ).getD index 0) form.gateCoefficients =
        φ (Finsupp.linearCombination ℂ
          (fun index => values.getD index 0) form.gateCoefficients) := by
    simpa [hgate, Function.comp_def] using
      (Finsupp.apply_linearCombination ℂ φ.toLinearMap
        (fun index => values.getD index 0) form.gateCoefficients).symm
  have hinputCombination :
      φ (Finsupp.linearCombination ℂ MvPolynomial.X
        form.inputCoefficients) =
        Finsupp.linearCombination ℂ
          (fun index => (substitution index).polynomial)
          form.inputCoefficients := by
    simpa [φ, Function.comp_def] using
      Finsupp.apply_linearCombination ℂ φ.toLinearMap
        (MvPolynomial.X : ι → MvPolynomial ι ℂ)
        form.inputCoefficients
  have hconstantCombination :
      (MvPolynomial.C
        (Finsupp.linearCombination ℂ
          (fun index => (substitution index).constant)
          form.inputCoefficients) : MvPolynomial κ ℂ) =
        Finsupp.linearCombination ℂ
          (fun index =>
            (MvPolynomial.C (substitution index).constant :
              MvPolynomial κ ℂ))
          form.inputCoefficients := by
    simpa [Function.comp_def, Algebra.linearMap_apply,
      MvPolynomial.algebraMap_eq] using
      Finsupp.apply_linearCombination ℂ
        (Algebra.linearMap ℂ (MvPolynomial κ ℂ))
        (fun index => (substitution index).constant)
        form.inputCoefficients
  have hlinearCombination :
      Finsupp.linearCombination ℂ
        (MvPolynomial.X : κ → MvPolynomial κ ℂ)
        (Finsupp.linearCombination ℂ
          (fun index => (substitution index).inputCoefficients)
          form.inputCoefficients) =
        Finsupp.linearCombination ℂ
          (fun index => Finsupp.linearCombination ℂ
            (MvPolynomial.X : κ → MvPolynomial κ ℂ)
            (substitution index).inputCoefficients)
          form.inputCoefficients := by
    simpa [Function.comp_def] using
      Finsupp.apply_linearCombination ℂ
        (Finsupp.linearCombination ℂ
          (MvPolynomial.X : κ → MvPolynomial κ ℂ))
        (fun index => (substitution index).inputCoefficients)
        form.inputCoefficients
  have hsplitCombination :
      Finsupp.linearCombination ℂ
        (fun index => (substitution index).polynomial)
        form.inputCoefficients =
      Finsupp.linearCombination ℂ
        (fun index => MvPolynomial.C (substitution index).constant)
        form.inputCoefficients +
      Finsupp.linearCombination ℂ
        (fun index => Finsupp.linearCombination ℂ
          (MvPolynomial.X : κ → MvPolynomial κ ℂ)
          (substitution index).inputCoefficients)
        form.inputCoefficients := by
    simp [Finsupp.linearCombination_apply, Finsupp.sum,
      FreeAffineInput.polynomial, Finset.sum_add_distrib, smul_add]
  change
    MvPolynomial.C
        (form.constant + Finsupp.linearCombination ℂ
          (fun index => (substitution index).constant)
          form.inputCoefficients) +
      Finsupp.linearCombination ℂ MvPolynomial.X
        (Finsupp.linearCombination ℂ
          (fun index => (substitution index).inputCoefficients)
          form.inputCoefficients) +
      Finsupp.linearCombination ℂ
        (fun index => (values.map φ).getD index 0)
        form.gateCoefficients =
      φ (MvPolynomial.C form.constant +
        Finsupp.linearCombination ℂ MvPolynomial.X
          form.inputCoefficients +
        Finsupp.linearCombination ℂ
          (fun index => values.getD index 0) form.gateCoefficients)
  rw [map_add, map_add, map_add, hconstantCombination,
    hlinearCombination, hinputCombination, hgateCombination,
    hsplitCombination]
  simp [φ, MvPolynomial.algebraMap_eq, add_assoc]
end PermanentRollout.FreeAffineForm
