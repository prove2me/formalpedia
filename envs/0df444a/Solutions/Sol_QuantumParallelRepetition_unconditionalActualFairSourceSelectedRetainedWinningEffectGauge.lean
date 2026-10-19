-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceSelectedRetainedWinningEffectGauge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/1097fd43-0910-46c8-baf4-70132dc978ab

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unitaryConjugatePOVM_jointEffect
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedGaugeRetainedPOVMNaturality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ}
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (x : X) (y : Y) :
    let e := physical8SelectedGlobalTargetWorkEquiv P N d m
    let U := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P alice
    let V := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P bob
    directDSVActualLocalPOVMWinningEffect G
      (directDSVActualReindexedRetainedPOVM e
        (unitaryConjugatePOVM alice PA))
      (directDSVActualReindexedRetainedPOVM e
        (unitaryConjugatePOVM bob PB)) x y =
      (((U : Matrix _ _ ℂ) ⊗ₖ (V : Matrix _ _ ℂ))ᴴ *
        directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e PA)
          (directDSVActualReindexedRetainedPOVM e PB) x y *
        ((U : Matrix _ _ ℂ) ⊗ₖ (V : Matrix _ _ ℂ))) := by
  classical
  dsimp only
  rw [unconditionalSelectedGaugeRetainedPOVMNaturality,
    unconditionalSelectedGaugeRetainedPOVMNaturality]
  unfold directDSVActualLocalPOVMWinningEffect
  simp_rw [unitaryConjugatePOVM_jointEffect]
  simp [Finset.mul_sum, Finset.sum_mul]
end QuantumParallelRepetition
