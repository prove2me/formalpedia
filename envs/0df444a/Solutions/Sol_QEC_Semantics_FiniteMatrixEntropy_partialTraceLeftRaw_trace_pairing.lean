-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:55:22.601039+00:00
-- url     : https://prove2.me/submissions/e453dfdc-2acf-41f9-8db3-11813cf5372c

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceRightRaw_trace_pairing
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator (CompositeSystem H K)) (Y : Operator K) :
    LinearMap.trace Complex K (((partialTraceLeftRaw H K) A).comp Y) =
      LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y)) := by
  let e : CompositeSystem H K ≃ₗ[Complex] CompositeSystem K H :=
    TensorProduct.comm Complex H K
  change LinearMap.trace Complex K
      (((partialTraceRightRaw K H) (e.conj A)).comp Y) = _
  let bH : OrthonormalBasis (ULift.{u} (Fin (Module.finrank Complex H))) Complex H :=
    (stdOrthonormalBasis Complex H).reindex Equiv.ulift.symm
  rw [partialTraceRightRaw_trace_pairing
    (H := K) (K := H) (bH) (e.conj A) Y]
  have hswap : e.symm.toLinearMap.comp
      ((TensorProduct.map Y (LinearMap.id : H →ₗ[Complex] H)).comp e.toLinearMap) =
        TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul h k => simp [e, LinearMap.comp_apply]
    | add x y hx hy => simp [map_add, hx, hy]
  have hconj : (e.conj A).comp
      (TensorProduct.map Y (LinearMap.id : H →ₗ[Complex] H)) =
        e.conj (A.comp (e.symm.toLinearMap.comp
          ((TensorProduct.map Y (LinearMap.id : H →ₗ[Complex] H)).comp e.toLinearMap))) := by
    simp [LinearEquiv.conj_apply, LinearMap.comp_assoc]
  rw [hconj, LinearMap.trace_conj', hswap]
end QEC.Semantics.FiniteMatrixEntropy
