-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485CompleteDecodedScalarBorn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/ad8b3649-1cac-455b-ab4d-3b31e8e9d77c

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485CompleteDecodedPhysicalBorn

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
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
    (selectedA :
      POVM A (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedB :
      POVM B (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedA_eq :
      selectedA =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PA)
    (selectedB_eq :
      selectedB =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PB)
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (rawA : POVM A ι) (rawB : POVM B κ)
    (rawA_eq :
      rawA =
        directDSVActualReindexedRetainedPOVM eA
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA)))
    (rawB_eq :
      rawB =
        directDSVActualReindexedRetainedPOVM eB
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (source cleaned : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (source_eq : source = cleaned)
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
              eA eB) z)) = cleaned) :
    unconditionalActualC485SelectedVerifierBorn
        G selectedA selectedB x y source =
      unconditionalActualC485RawPhysicalVerifierBorn
        G rawA rawB x y z := by
  exact unconditionalActualC485CompleteDecodedPhysicalBorn
    G alice bob PA PB selectedA selectedB selectedA_eq selectedB_eq
    eA eB pair rawA rawB rawA_eq rawB_eq
    x y z source cleaned source_eq decoded
end QuantumParallelRepetition
