-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_leftBlock_of_lifted_coefficient_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:43:44.770033+00:00
-- url     : https://prove2.me/submissions/9f9b4d55-7894-428b-b154-b379c9fb09f6

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_unitaryLTensor_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_rightTensorExtensionAfterLeft_of_leftInteractionCoefficients_tensor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_overlapProjectorOnIsotypicComponent
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_norm_isotypicLiftedMultiplicityUnitVector

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
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B)
    (n : Nat) [NeZero n] (W : Submodule (leftInteractionAlgebra P) B)
    (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n))
    (hleft : ∀ a a' : A,
      U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
        TensorProduct.map
          (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩)
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n))) :
    ∃ Pleft : Semantics.Operator (Semantics.CompositeSystem A (W.restrictScalars Complex)),
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent P component) =
        rightTensorExtensionAfterLeft A (W.restrictScalars Complex)
          (isotypicLiftedMultiplicity.{u} n) Pleft := by
  let etaN := isotypicLiftedMultiplicityUnitVector.{u} n
  have hetaN : ‖etaN‖ = 1 := norm_isotypicLiftedMultiplicityUnitVector.{u} n
  have hcoefficients : ∀ a a' : A,
      ∃ R : Semantics.Operator (W.restrictScalars Complex),
        leftInteractionCoefficient
            ((unitaryLTensor A U).conjOperator
              (overlapProjectorOnIsotypicComponent P component)) a a' =
          TensorProduct.map R
            (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := by
    intro a a'
    let coefficient : leftInteractionAlgebra P :=
      ⟨leftInteractionCoefficient P a a',
        leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩
    refine ⟨isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient, ?_⟩
    calc
      leftInteractionCoefficient
          ((unitaryLTensor A U).conjOperator
            (overlapProjectorOnIsotypicComponent P component)) a a' =
          U.conjOperator
            (leftInteractionCoefficient
              (overlapProjectorOnIsotypicComponent P component) a a') :=
        leftInteractionCoefficient_unitaryLTensor_conjOperator U
          (overlapProjectorOnIsotypicComponent P component) a a'
      _ = U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component coefficient) := by
            exact congrArg U.conjOperator
              (leftInteractionCoefficient_overlapProjectorOnIsotypicComponent P component a a')
      _ = TensorProduct.map
          (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient)
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := hleft a a'
  exact exists_rightTensorExtensionAfterLeft_of_leftInteractionCoefficients_tensor
    A (W.restrictScalars Complex) (isotypicLiftedMultiplicity.{u} n)
    ((unitaryLTensor A U).conjOperator
      (overlapProjectorOnIsotypicComponent P component)) etaN hetaN hcoefficients
end QEC.Bounds.BPTCommutingProjectorModel
