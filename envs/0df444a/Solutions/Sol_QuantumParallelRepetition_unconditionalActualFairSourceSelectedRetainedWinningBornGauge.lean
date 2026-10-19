-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceSelectedRetainedWinningBornGauge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/e7bb44e1-ced1-4ee6-bf58-b4498ea17b0b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_rectangular_matrix_quadratic_compression
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceSelectedRetainedWinningEffectGauge

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
    {X Y A B τ : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype τ] [DecidableEq τ]
    {P N d m : ℕ}
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × τ)) :
    let e := physical8SelectedGlobalTargetWorkEquiv P N d m
    let U := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P alice
    let V := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P bob
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m) × τ)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e
            (unitaryConjugatePOVM alice PA))
          (directDSVActualReindexedRetainedPOVM e
            (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
          (1 : Matrix τ τ ℂ))) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m) × τ)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e PA)
          (directDSVActualReindexedRetainedPOVM e PB) x y ⊗ₖ
          (1 : Matrix τ τ ℂ)))
      (unconditionalMixedConjugateSelectedBranchLocalAction
        U V z) := by
  classical
  dsimp only
  rw [unconditionalActualFairSourceSelectedRetainedWinningEffectGauge]
  let UA := unconditionalMixedConjugateSigmaAtomLift
    (m := N * m) P alice
  let UB := unconditionalMixedConjugateSigmaAtomLift
    (m := N * m) P bob
  let e := physical8SelectedGlobalTargetWorkEquiv P N d m
  let selected : Type := UnconditionalSelectedCopyLocalIndex P d N m
  let E : Matrix (selected × selected) (selected × selected) ℂ :=
    directDSVActualLocalPOVMWinningEffect G
      (directDSVActualReindexedRetainedPOVM e PA)
      (directDSVActualReindexedRetainedPOVM e PB) x y
  let K : Matrix (selected × selected) (selected × selected) ℂ :=
    (UA : Matrix selected selected ℂ) ⊗ₖ
      (UB : Matrix selected selected ℂ)
  let W : Matrix ((selected × selected) × τ)
      ((selected × selected) × τ) ℂ :=
    K ⊗ₖ (1 : Matrix τ τ ℂ)
  have transport :
      (Kᴴ * E * K) ⊗ₖ (1 : Matrix τ τ ℂ) =
        Wᴴ * (E ⊗ₖ (1 : Matrix τ τ ℂ)) * W := by
    calc
      (Kᴴ * E * K) ⊗ₖ (1 : Matrix τ τ ℂ) =
          (Kᴴ ⊗ₖ (1 : Matrix τ τ ℂ)) *
            (E ⊗ₖ (1 : Matrix τ τ ℂ)) *
            (K ⊗ₖ (1 : Matrix τ τ ℂ)) := by
              rw [← Matrix.mul_kronecker_mul,
                ← Matrix.mul_kronecker_mul]
              simp
      _ = Wᴴ * (E ⊗ₖ (1 : Matrix τ τ ℂ)) * W := by
        simp [W, Matrix.conjTranspose_kronecker]
  change
    quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (selected × selected) × τ) (𝕜 := ℂ)
          ((Kᴴ * E * K) ⊗ₖ (1 : Matrix τ τ ℂ))) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (selected × selected) × τ) (𝕜 := ℂ)
          (E ⊗ₖ (1 : Matrix τ τ ℂ)))
        (unconditionalMixedConjugateSelectedBranchLocalAction
          UA UB z)
  rw [transport]
  exact (rectangular_matrix_quadratic_compression
    W (E ⊗ₖ (1 : Matrix τ τ ℂ)) z).symm
end QuantumParallelRepetition
