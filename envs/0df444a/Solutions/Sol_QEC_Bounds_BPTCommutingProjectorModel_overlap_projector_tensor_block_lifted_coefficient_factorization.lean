-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.overlap_projector_tensor_block_lifted_coefficient_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:58.795079+00:00
-- url     : https://prove2.me/submissions/ad77b748-8da6-4cc3-8945-69968da552e4

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_left
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_right
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_tensor_block_coefficient_factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



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
    (n : Nat) (W : Submodule (leftInteractionAlgebra P) B)
    (hW : IsSimpleModule (leftInteractionAlgebra P) W)
    (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (W.restrictScalars Complex ⊗[Complex] isotypicLiftedMultiplicity.{u} n),
      (∀ a a' : A,
        U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component
            ⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
          TensorProduct.map
            (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W
              ⟨leftInteractionCoefficient P a a',
                leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩)
            (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n))) ∧
      (∀ c c' : C, ∃ R : Semantics.Operator (isotypicLiftedMultiplicity.{u} n),
        U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
          TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by
  letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
  rcases overlap_projector_tensor_block_coefficient_factorization P Q hselfAdjoint hcommute
    component n W hW e with ⟨U0, hleft, hright⟩
  let V := isotypicMultiplicityLiftTensorUnitary (W.restrictScalars Complex) n
  let U := composeUnitaryTransport U0 V
  refine ⟨U, ?_, ?_⟩
  · intro a a'
    let coefficient : leftInteractionAlgebra P :=
      ⟨leftInteractionCoefficient P a a',
        leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩
    calc
      U.conjOperator
          (isotypicLeftAction (leftInteractionAlgebra P) component coefficient) =
          V.conjOperator
            (U0.conjOperator
              (isotypicLeftAction (leftInteractionAlgebra P) component coefficient)) := by
            exact composeUnitaryTransport_conjOperator U0 V
              (isotypicLeftAction (leftInteractionAlgebra P) component coefficient)
      _ = V.conjOperator
          (isotypicTensorLeftAction (leftInteractionAlgebra P) W n coefficient) := by
            rw [hleft a a']
      _ = TensorProduct.map
          (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient)
          (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := by
            dsimp [V]
            simpa [isotypicTensorLeftAction] using
              (isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_left
                (W.restrictScalars Complex) n
                (isotypicLeftActionOnSimple (leftInteractionAlgebra P) W coefficient))
  · intro c c'
    rcases hright c c' with ⟨R, hR⟩
    refine ⟨isotypicMultiplicityLiftConjOperator.{u} n R, ?_⟩
    calc
      U.conjOperator
          (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
            component c c') =
          V.conjOperator
            (U0.conjOperator
              (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
                component c c')) := by
            exact composeUnitaryTransport_conjOperator U0 V
              (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
                component c c')
      _ = V.conjOperator
          (TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by
            rw [hR]
      _ = TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
          (isotypicMultiplicityLiftConjOperator.{u} n R) := by
            dsimp [V]
            exact isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_right
              (W.restrictScalars Complex) n R
end QEC.Bounds.BPTCommutingProjectorModel
