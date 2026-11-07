-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCut_overlap_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:24.113004+00:00
-- url     : https://prove2.me/submissions/9e22bdef-012f-4c3f-a92d-5cc1890f1cae

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_mul_BC_commute_projectorCD
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_CD_eq_sourceCD
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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region))
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) := by
  let U := M.firstCutCoordinateTransport region
  let P := overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)
  let Q := overlapLiftRight
    (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (M.fourFactorProjectorCDLocal region)
  have hP : U.conjOperator P = (M.fourFactorTransport region).conjOperator
      (M.projectorAB region * M.projectorBC region) := by
    dsimp [U, P]
    exact M.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC region
  have hQ : U.conjOperator Q =
      (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
    dsimp [U, Q]
    exact M.firstCutCoordinateTransport_conj_CD_eq_sourceCD region
  have hsource : Commute
      ((M.fourFactorTransport region).conjOperator (M.projectorAB region * M.projectorBC region))
      ((M.fourFactorTransport region).conjOperator (M.projectorCD region)) := by
    change (M.fourFactorTransport region).conjOperator
        (M.projectorAB region * M.projectorBC region) *
        (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
      (M.fourFactorTransport region).conjOperator (M.projectorCD region) *
        (M.fourFactorTransport region).conjOperator
          (M.projectorAB region * M.projectorBC region)
    calc
      (M.fourFactorTransport region).conjOperator
          (M.projectorAB region * M.projectorBC region) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
          (M.fourFactorTransport region).conjOperator
            ((M.projectorAB region * M.projectorBC region) * M.projectorCD region) :=
        (Semantics.UnitaryTransport.conjOperator_mul
          (M.fourFactorTransport region)
          (M.projectorAB region * M.projectorBC region) (M.projectorCD region)).symm
      _ = (M.fourFactorTransport region).conjOperator
            (M.projectorCD region * (M.projectorAB region * M.projectorBC region)) :=
        congrArg (M.fourFactorTransport region).conjOperator
          (M.projectorAB_mul_BC_commute_projectorCD region).eq
      _ = (M.fourFactorTransport region).conjOperator (M.projectorCD region) *
          (M.fourFactorTransport region).conjOperator
            (M.projectorAB region * M.projectorBC region) :=
        Semantics.UnitaryTransport.conjOperator_mul
          (M.fourFactorTransport region) (M.projectorCD region)
          (M.projectorAB region * M.projectorBC region)
  have htransport : U.conjOperator (P * Q) = U.conjOperator (Q * P) := by
    calc
      U.conjOperator (P * Q) = U.conjOperator P * U.conjOperator Q :=
        Semantics.UnitaryTransport.conjOperator_mul U P Q
      _ = U.conjOperator Q * U.conjOperator P := by
        rw [hP, hQ]
        exact hsource
      _ = U.conjOperator (Q * P) :=
        (Semantics.UnitaryTransport.conjOperator_mul U Q P).symm
  change P * Q = Q * P
  calc
    P * Q = U.symm.conjOperator (U.conjOperator (P * Q)) :=
      (Semantics.UnitaryTransport.symm_conjOperator_conjOperator U (P * Q)).symm
    _ = U.symm.conjOperator (U.conjOperator (Q * P)) := congrArg U.symm.conjOperator htransport
    _ = Q * P := Semantics.UnitaryTransport.symm_conjOperator_conjOperator U (Q * P)
end QEC.Bounds.BPTCommutingProjectorModel
