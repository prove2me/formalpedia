-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.overlap_product_commutes_leftIsotypicSectorLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:46:15.934213+00:00
-- url     : https://prove2.me/submissions/1f625ae9-969d-4558-9a9e-02181ebbe505

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_commutes_overlap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap
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
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Commute
      (overlapLiftLeft (C := C) P * overlapLiftRight (A := A) Q)
      (overlapLiftLeft (C := C)
        (TensorProduct.map (1 : Semantics.Operator A)
          (leftIsotypicSectorProjector P component))) := by
  let sector := leftIsotypicSectorProjector P component
  let sectorLift := overlapLiftLeft (C := C)
    (TensorProduct.map (1 : Semantics.Operator A) sector)
  have hsectorCommutes := leftIsotypicSectorProjector_commutes_overlap
    P Q hselfAdjoint hcommute component
  have hPcommutes : Commute (overlapLiftLeft (C := C) P) sectorLift := by
    change TensorProduct.map P (1 : Semantics.Operator C) *
        TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator C) =
      TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) sector)
          (1 : Semantics.Operator C) * TensorProduct.map P (1 : Semantics.Operator C)
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
    simpa using congrArg (fun operator =>
      TensorProduct.map operator (1 : Semantics.Operator C)) hsectorCommutes.1.eq
  have hsectorLiftRight : sectorLift =
      overlapLiftRight (A := A) (TensorProduct.map sector (1 : Semantics.Operator C)) := by
    dsimp [sectorLift, overlapLiftLeft, overlapLiftRight]
    symm
    exact tensorAssociatorUnitary_symm_conj_tensorMap
      (1 : Semantics.Operator A) sector (1 : Semantics.Operator C)
  have hQcommutes : Commute (overlapLiftRight (A := A) Q) sectorLift := by
    rw [hsectorLiftRight]
    change Commute
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A) Q))
      ((tensorAssociatorUnitary A B C).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map sector (1 : Semantics.Operator C))))
    calc
      (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A) Q) *
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator C))) =
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q *
              TensorProduct.map (1 : Semantics.Operator A)
                (TensorProduct.map sector (1 : Semantics.Operator C))) :=
          (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map sector (1 : Semantics.Operator C)) *
              TensorProduct.map (1 : Semantics.Operator A) Q) := by
          congr 1
          rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
          simpa using congrArg (fun operator =>
            TensorProduct.map (1 : Semantics.Operator A) operator) hsectorCommutes.2.eq
      _ = (tensorAssociatorUnitary A B C).symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map sector (1 : Semantics.Operator C))) *
          (tensorAssociatorUnitary A B C).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A) Q) :=
          Semantics.UnitaryTransport.conjOperator_mul _ _ _
  exact (hPcommutes.symm.mul_right hQcommutes.symm).symm
end QEC.Bounds.BPTCommutingProjectorModel
