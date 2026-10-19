-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMixedConjugateSigmaAtomLift_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/5d23b3c5-f73d-46ca-b62d-bb0d72042d09

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d m : ℕ} (B : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    (unconditionalMixedConjugateSigmaAtomLift (m := m) B U :
      Matrix (Σ _ : Fin B × Fin d, Fin m)
        (Σ _ : Fin B × Fin d, Fin m) ℂ)
      ⟨(φ, i), a⟩ ⟨(ψ, j), b⟩ =
      if φ = ψ ∧ a = b then
        (U : Matrix (Fin d) (Fin d) ℂ) i j
      else 0 := by
  classical
  by_cases phase : φ = ψ <;>
    by_cases work : a = b <;>
      simp [unconditionalMixedConjugateSigmaAtomLift,
        Matrix.reindex_apply, Matrix.kroneckerMap_apply, phase, work]
end QuantumParallelRepetition
