-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_blocks_single_sector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:38.114238+00:00
-- url     : https://prove2.me/submissions/3f9bdd79-fea0-4ee5-995d-27187cd54bab

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_tensor_block_lifted_coefficient_factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_leftBlock_of_lifted_coefficient_factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_rightBlock_of_lifted_coefficient_factorization

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) [NeZero n] (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)) :
    ∃ (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
        (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)))
      (Qright : Semantics.Operator
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{u} n) C)),
      (unitaryLTensor A U).conjOperator
        (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft ∧
      (unitaryRTensor U C).conjOperator
        (overlapRightProjectorOnIsotypicComponent P Q component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) C Qright := by
  letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
  rcases overlap_projector_tensor_block_lifted_coefficient_factorization
    P Q hselfAdjoint hcommute component n W hW e with ⟨U, hleft, hright⟩
  rcases overlap_projector_leftBlock_of_lifted_coefficient_factorization
    P component n W U hleft with ⟨Pleft, hPleft⟩
  rcases overlap_projector_rightBlock_of_lifted_coefficient_factorization
    P Q hselfAdjoint hcommute component n W hW U hright with ⟨Qright, hQright⟩
  exact ⟨U, Pleft, Qright, hPleft, hQright⟩
end QEC.Bounds.BPTCommutingProjectorModel
