-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.selectedPartialTraceFromRegister_rankOne_eq_smul_selectedMarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:10:20.272284+00:00
-- url     : https://prove2.me/submissions/762c7ea1-afdd-4c52-be40-d9c2988bebae

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_allSelected_detectableOn
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedPartialTraceFromRegister_trace_pairing
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_eq_scalar_of_supported_detectableOnWithScalar
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_rankOne_comp
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho)
    (x y : Qudit.QuditRegister q) (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) :
    S.selectedPartialTraceFromRegister
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  let X : Operator S.selectedSystem :=
    (InnerProductSpace.rankOne Complex v u).toLinearMap
  rcases S.erasureRecovery_allSelected_detectableOn C recovery hcorrect X with ⟨c, hdetect⟩
  have htrace_rho : LinearMap.trace Complex S.selectedSystem
      ((S.selectedPartialTraceFromRegister rho.toOperator).comp X) = c := by
    calc
      LinearMap.trace Complex S.selectedSystem
          ((S.selectedPartialTraceFromRegister rho.toOperator).comp X) =
          LinearMap.trace Complex (Qudit.QuditRegister q)
            (rho.toOperator.comp (S.extendLocalToRegister X)) :=
              S.selectedPartialTraceFromRegister_trace_pairing rho.toOperator X
      _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((S.extendLocalToRegister X).comp rho.toOperator) :=
            (LinearMap.trace_comp_comm' rho.toOperator (S.extendLocalToRegister X)).symm
      _ = c := trace_comp_eq_scalar_of_supported_detectableOnWithScalar C
        (S.extendLocalToRegister X) c hdetect rho hsupported
  calc
    inner Complex u
        (S.selectedPartialTraceFromRegister
          (InnerProductSpace.rankOne Complex x y).toLinearMap v) =
        LinearMap.trace Complex S.selectedSystem
          ((S.selectedPartialTraceFromRegister
            (InnerProductSpace.rankOne Complex x y).toLinearMap).comp X) := by
              simpa [X] using
                (trace_comp_rankOne
                  (S.selectedPartialTraceFromRegister
                    (InnerProductSpace.rankOne Complex x y).toLinearMap) v u).symm
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
        ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp
          (S.extendLocalToRegister X)) :=
            S.selectedPartialTraceFromRegister_trace_pairing
              (InnerProductSpace.rankOne Complex x y).toLinearMap X
    _ = inner Complex y ((S.extendLocalToRegister X) x) :=
          trace_rankOne_comp (S.extendLocalToRegister X) x y
    _ = c * inner Complex y x := hdetect y hy x hx
    _ = (inner Complex y x) * c := by ring
    _ = (inner Complex y x) * LinearMap.trace Complex S.selectedSystem
        ((S.selectedPartialTraceFromRegister rho.toOperator).comp X) := by
          rw [htrace_rho]
    _ = LinearMap.trace Complex S.selectedSystem
        (((inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator).comp X) := by
          simp [LinearMap.smul_comp, smul_eq_mul]
    _ = inner Complex u
        (((inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator) v) := by
          simpa [X] using
            trace_comp_rankOne
              ((inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator) v u
end QEC.Semantics.QuditSubsystem
