-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.leftInteractionCoefficient_overlapProjectorOnIsotypicComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:41:12.675475+00:00
-- url     : https://prove2.me/submissions/2c7050ed-01e1-465e-a822-d8beb9299b12

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_right_comp_overlapLeftEmbedding_hom
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapLeftEmbedding_comp_tensorMap_right_adjoint_hom
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_submoduleSubtype_apply_subtype
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
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (a a' : A) :
    leftInteractionCoefficient (overlapProjectorOnIsotypicComponent P component) a a' =
      isotypicLeftAction (leftInteractionAlgebra P) component
        ⟨leftInteractionCoefficient P a a',
          leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ := by
  let inclusion := (component.1.restrictScalars Complex).subtype
  let coefficient : leftInteractionAlgebra P :=
    ⟨leftInteractionCoefficient P a a',
      leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩
  have haction :
      inclusion.comp
        (isotypicLeftAction (leftInteractionAlgebra P) component coefficient) =
        (coefficient : Semantics.Operator B).comp inclusion := by
    rfl
  unfold leftInteractionCoefficient overlapProjectorOnIsotypicComponent
  change
    (LinearMap.adjoint
      (overlapLeftEmbedding A (component.1.restrictScalars Complex) a)).comp
      (((TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint inclusion)).comp
        (P.comp (TensorProduct.map (1 : Semantics.Operator A) inclusion))).comp
          (overlapLeftEmbedding A (component.1.restrictScalars Complex) a')) =
      isotypicLeftAction (leftInteractionAlgebra P) component coefficient
  calc
    _ = ((LinearMap.adjoint (overlapLeftEmbedding A (component.1.restrictScalars Complex) a)).comp
          (TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint inclusion))).comp
        (P.comp ((TensorProduct.map (1 : Semantics.Operator A) inclusion).comp
          (overlapLeftEmbedding A (component.1.restrictScalars Complex) a'))) := by
          simp only [LinearMap.comp_assoc]
    _ = ((LinearMap.adjoint inclusion).comp
          (LinearMap.adjoint (overlapLeftEmbedding A B a))).comp
        (P.comp ((overlapLeftEmbedding A B a').comp inclusion)) := by
          rw [adjoint_overlapLeftEmbedding_comp_tensorMap_right_adjoint_hom (A := A) a inclusion,
            tensorMap_right_comp_overlapLeftEmbedding_hom (A := A) a' inclusion]
    _ = (LinearMap.adjoint inclusion).comp
        ((leftInteractionCoefficient P a a').comp inclusion) := by
          simp only [leftInteractionCoefficient, LinearMap.comp_assoc]
    _ = isotypicLeftAction (leftInteractionAlgebra P) component coefficient := by
          apply LinearMap.ext
          intro vector
          have hactionApply :
              inclusion
                (isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector) =
              (leftInteractionCoefficient P a a') (inclusion vector) := by
            exact congrArg (fun map => map vector) haction
          change LinearMap.adjoint inclusion
              ((leftInteractionCoefficient P a a') (inclusion vector)) =
            isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector
          calc
            LinearMap.adjoint inclusion
                ((leftInteractionCoefficient P a a') (inclusion vector)) =
                LinearMap.adjoint inclusion
                  (inclusion
                    (isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector)) := by
                      exact congrArg (LinearMap.adjoint inclusion) hactionApply.symm
            _ = isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector := by
                  exact adjoint_submoduleSubtype_apply_subtype
                    (component.1.restrictScalars Complex)
                    (isotypicLeftAction (leftInteractionAlgebra P) component coefficient vector)
end QEC.Bounds.BPTCommutingProjectorModel
