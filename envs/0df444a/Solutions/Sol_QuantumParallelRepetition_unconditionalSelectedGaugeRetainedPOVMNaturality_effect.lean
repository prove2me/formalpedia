-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedGaugeRetainedPOVMNaturality_effect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/1689db03-b2a8-4fc5-a575-6af78b3ba407

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSigmaAtomLift_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {C : Type} [Fintype C]
    {P N d m : ℕ}
    (basis : Matrix.unitaryGroup (Fin d) ℂ)
    (source : POVM C (Fin d)) (a : C) :
    (directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv P N d m)
      (unitaryConjugatePOVM basis source)).effect a =
    (unitaryConjugatePOVM
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P basis)
      (directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        source)).effect a := by
  classical
  ext p q
  rcases p with ⟨⟨φ, i⟩, k⟩
  rcases q with ⟨⟨ψ, j⟩, l⟩
  by_cases phase : φ = ψ <;> by_cases work : k = l <;>
    simp [directDSVActualReindexedRetainedPOVM_effect,
      physical8SelectedGlobalTargetWorkEquiv,
      unitaryConjugatePOVM, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sigma,
      Fintype.sum_prod_type,
      unconditionalMixedConjugateSigmaAtomLift_apply,
      mul_assoc, ite_and, phase, work, eq_comm]
end QuantumParallelRepetition
