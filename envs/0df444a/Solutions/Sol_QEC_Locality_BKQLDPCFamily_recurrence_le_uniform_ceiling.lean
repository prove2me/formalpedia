-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.recurrence_le_uniform_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:43:09.273733+00:00
-- url     : https://prove2.me/submissions/84610789-6d01-44ea-9382-a1588dc24aa2

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_bkEntropyGap_pos
import Theorems.Thm_QEC_Locality_bkRpowCoefficient_le_entropy_bound
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_cMax_coefficient
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_cMax_lt_one
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_cMax_nonneg
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {ceiling : ℝ} (_hceiling0 : 0 ≤ ceiling) (hceiling1 : ceiling < 1)
    (hcMax : family.cMax i ≤ ceiling) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
  have hbase := family.recurrence_le_cMax_coefficient i
  have hpointwiseCoeff := bkRpowCoefficient_le_entropy_bound
    (beta := (1 : ℝ)) (c := family.cMax i) (by norm_num)
      (family.cMax_nonneg i) (family.cMax_lt_one i)
  have hceilingDenomPos : 0 < bkEntropyGap * (1 - ceiling) :=
    mul_pos bkEntropyGap_pos (sub_pos.mpr hceiling1)
  have hdenomOrder :
      bkEntropyGap * (1 - ceiling) ≤
        bkEntropyGap * (1 - family.cMax i) := by
    exact mul_le_mul_of_nonneg_left (by linarith) bkEntropyGap_pos.le
  have huniformCoeff :
      bkRpowCoefficient 1 (family.cMax i) ≤
        3 / (bkEntropyGap * (1 - ceiling)) := by
    have hdiv :
        (3 : ℝ) / (bkEntropyGap * (1 - family.cMax i)) ≤
          3 / (bkEntropyGap * (1 - ceiling)) :=
      div_le_div_of_nonneg_left (by norm_num) hceilingDenomPos hdenomOrder
    have hpointwiseCoeff' :
        bkRpowCoefficient 1 (family.cMax i) ≤
          3 / (bkEntropyGap * (1 - family.cMax i)) := by
      simpa using hpointwiseCoeff
    exact hpointwiseCoeff'.trans hdiv
  have hparentNonneg : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg i.1
  have hdistancePos : (0 : ℝ) < family.distance i.1 := by
    have hdNat : 0 < family.distance i.1 := by
      have hdTwo : 2 ≤ family.distance i.1 := by
        simpa [distance] using family.distance_two_le i.1 i.2
      omega
    exact_mod_cast hdNat
  have hdenomPos : 0 <
      (family.distance i.1 : ℝ) ^ (1 - family.cMax i) :=
    Real.rpow_pos_of_pos hdistancePos _
  calc
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
        bkRpowCoefficient 1 (family.cMax i) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := hbase
    _ ≤ (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right huniformCoeff hparentNonneg) hdenomPos.le
end QEC.Locality.BKQLDPCFamily
