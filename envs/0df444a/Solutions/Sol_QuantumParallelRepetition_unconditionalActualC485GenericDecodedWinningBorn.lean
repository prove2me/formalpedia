-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485GenericDecodedWinningBorn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/4987e5da-fbf1-4864-9cae-6b8e6532611d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485GenericSelectedWinningRegroupGauge

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (actual : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = actual) :
    let selected := UnconditionalSelectedCopyLocalIndex P d N m
    let stage := physical8SelectedGlobalTargetWorkEquiv P N d m
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (selected × selected) × T) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM stage PA)
          (directDSVActualReindexedRetainedPOVM stage PB)
          x y ⊗ₖ (1 : Matrix T T ℂ))) actual =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM eA
              (directDSVActualReindexedRetainedPOVM stage
                (unitaryConjugatePOVM alice PA)))
            (directDSVActualReindexedRetainedPOVM eB
              (directDSVActualReindexedRetainedPOVM stage
                (unitaryConjugatePOVM bob PB))) x y)) z := by
  dsimp only
  have physical :=
    unconditionalActualC485GenericSelectedWinningRegroupGauge
      G alice bob PA PB eA eB pair x y z
  dsimp only at physical
  rw [decoded] at physical
  exact physical.symm
end QuantumParallelRepetition
