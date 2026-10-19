-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedGaugeRetainedPOVMNaturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/f00a68fb-7536-4182-a398-1c39602db35d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualRetainedPOVM_ext
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedGaugeRetainedPOVMNaturality_effect

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
    (source : POVM C (Fin d)) :
    directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        (unitaryConjugatePOVM basis source) =
      unitaryConjugatePOVM
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P basis)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          source) := by
  classical
  apply unconditionalActualRetainedPOVM_ext
  intro a i j
  exact congrArg (fun M => M i j)
    (unconditionalSelectedGaugeRetainedPOVMNaturality_effect
      (P := P) (N := N) (m := m) basis source a)
end QuantumParallelRepetition
