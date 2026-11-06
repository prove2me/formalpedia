-- Prove2me | solution 1 for QEC.Locality.erasureChannel_apply_eq_leftCompression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:53:29.491387+00:00
-- url     : https://prove2.me/submissions/355bf38a-2f4c-411d-91c8-5a9d4b0ddb43

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_partialTraceRightRaw_eq_rightCompression
import Theorems.Thm_QEC_Locality_factorSwap_symm_comp_tensorRight
import Theorems.Thm_QEC_Locality_tensorRight_adjoint_comp_factorSwap
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



set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem) :
    S.erasureChannel A = leftCompression S A := by
  change partialTraceRightRaw S.complementSystem S.selectedSystem
      (S.factorSwap.conjOperator A) = leftCompression S A
  rw [partialTraceRightRaw_eq_rightCompression S.complementSystem S.selectedSystem
    (EuclideanSpace.basisFun (Qubit.Bitstring S.SelectedCoordinates) Complex)]
  simp only [rightCompression, leftCompression, LinearMap.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  change
    (LinearMap.adjoint
        (tensorRight S.complementSystem S.selectedSystem (ket h))).comp
        ((S.factorSwap.conjOperator A).comp
          (tensorRight S.complementSystem S.selectedSystem (ket h))) =
      (LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket h))).comp
        (A.comp (tensorLeft S.selectedSystem S.complementSystem (ket h)))
  rw [show S.factorSwap.conjOperator A =
      S.factorSwap.toLinearEquiv.toLinearMap.comp
        (A.comp S.factorSwap.symm.toLinearEquiv.toLinearMap) by rfl]
  apply LinearMap.ext
  intro k
  simp only [LinearMap.comp_apply]
  have hright : S.factorSwap.symm.toLinearEquiv.toLinearMap
      ((tensorRight S.complementSystem S.selectedSystem (ket h)) k) =
      (tensorLeft S.selectedSystem S.complementSystem (ket h)) k := by
    exact DFunLike.congr_fun (factorSwap_symm_comp_tensorRight S h) k
  rw [hright]
  simpa only [LinearMap.comp_apply] using DFunLike.congr_fun
    (tensorRight_adjoint_comp_factorSwap S h)
    (A ((tensorLeft S.selectedSystem S.complementSystem (ket h)) k))
end QEC.Locality
