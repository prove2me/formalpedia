-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_rightBlock_of_lifted_coefficient_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:51:02.522943+00:00
-- url     : https://prove2.me/submissions/75f7d0a0-f4cc-4be3-8d28-44c163823415

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_unitaryRTensor_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_normalized_vector_of_nontrivial
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_leftTensorExtensionBeforeRight_of_rightInteractionCoefficients_tensor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_overlapRightProjectorOnIsotypicComponent

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
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
    (hright : ∀ c c' : C, ∃ R : Semantics.Operator (isotypicLiftedMultiplicity.{u} n),
      U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
        TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) :
    ∃ Qright : Semantics.Operator
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{u} n) C),
      (unitaryRTensor U C).conjOperator
          (overlapRightProjectorOnIsotypicComponent P Q component) =
        leftTensorExtensionBeforeRight (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) C Qright := by
  letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
  letI : Nontrivial (W.restrictScalars Complex) :=
    IsSimpleModule.nontrivial (leftInteractionAlgebra P) W
  rcases exists_normalized_vector_of_nontrivial
    (H := W.restrictScalars Complex) with ⟨etaW, hetaW⟩
  have hcoefficients : ∀ c c' : C,
      ∃ R : Semantics.Operator (isotypicLiftedMultiplicity.{u} n),
        rightInteractionCoefficient
            ((unitaryRTensor U C).conjOperator
              (overlapRightProjectorOnIsotypicComponent P Q component)) c c' =
          TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R := by
    intro c c'
    rcases hright c c' with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    calc
      rightInteractionCoefficient
          ((unitaryRTensor U C).conjOperator
            (overlapRightProjectorOnIsotypicComponent P Q component)) c c' =
          U.conjOperator
            (rightInteractionCoefficient
              (overlapRightProjectorOnIsotypicComponent P Q component) c c') :=
        rightInteractionCoefficient_unitaryRTensor_conjOperator U
          (overlapRightProjectorOnIsotypicComponent P Q component) c c'
      _ = U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') := by
            exact congrArg U.conjOperator
              (rightInteractionCoefficient_overlapRightProjectorOnIsotypicComponent
                P Q hselfAdjoint hcommute component c c')
      _ = TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R := hR
  exact exists_leftTensorExtensionBeforeRight_of_rightInteractionCoefficients_tensor
    (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{u} n) C
    ((unitaryRTensor U C).conjOperator
      (overlapRightProjectorOnIsotypicComponent P Q component)) etaW hetaW hcoefficients
end QEC.Bounds.BPTCommutingProjectorModel
