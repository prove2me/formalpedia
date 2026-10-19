-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485GenericSelectedWinningRegroupGauge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/80d0f642-17e2-490f-acb5-d2bb888ec1a0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceSelectedRetainedWinningBornGauge
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485RetainedPureWorkReindexBorn
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485GenericRetainedWinningBorn

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
    (z : EuclideanSpace ℂ (ι × κ)) :
    let selected := UnconditionalSelectedCopyLocalIndex P d N m
    let stage := physical8SelectedGlobalTargetWorkEquiv P N d m
    let gaugedAlice := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM alice PA)
    let gaugedBob := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM bob PB)
    let plainAlice := directDSVActualReindexedRetainedPOVM stage PA
    let plainBob := directDSVActualReindexedRetainedPOVM stage PB
    let regrouped :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr (Equiv.refl (selected × selected)) pair)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z)
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA gaugedAlice)
          (directDSVActualReindexedRetainedPOVM eB gaugedBob)
          x y)) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (selected × selected) × T) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          plainAlice plainBob x y ⊗ₖ (1 : Matrix T T ℂ)))
      (unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        regrouped) := by
  dsimp only
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) ×
              (R × R))
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM alice PA))
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
            (1 : Matrix (R × R) (R × R) ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z) :=
      unconditionalActualC485GenericRetainedWinningBorn
        G eA eB
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM alice PA))
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM bob PB)) x y z
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) × T)
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM alice PA))
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
            (1 : Matrix T T ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv eA eB) z)) :=
      unconditionalActualC485RetainedPureWorkReindexBorn
        pair
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA))
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)) x y)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z)
    _ = _ :=
      unconditionalActualFairSourceSelectedRetainedWinningBornGauge
        G alice bob PA PB x y
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv eA eB) z))
end QuantumParallelRepetition
