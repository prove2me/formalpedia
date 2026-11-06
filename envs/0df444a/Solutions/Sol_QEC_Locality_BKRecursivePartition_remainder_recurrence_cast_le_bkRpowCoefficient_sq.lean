-- Prove2me | solution 1 for QEC.Locality.BKRecursivePartition.remainder_recurrence_cast_le_bkRpowCoefficient_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:14:17.969444+00:00
-- url     : https://prove2.me/submissions/b4df87bb-7f88-4099-a816-effb8fd6a108

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_bkRpowCoefficient_nonneg
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_card_le_bkSumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_zero_of_terminal
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
namespace QEC.Locality
namespace BKRecursivePartition
theorem _root_.solution
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hvertices : d ≤ vertices.card)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ vertices.card →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤
      (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * vertices.card /
        (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by
  let coefficient := bkRpowCoefficient beta c
  let denominator := (d : ℝ) ^ (1 - c)
  have hdPos : 0 < d := by omega
  have hdenominatorPos : 0 < denominator := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hdPos) _
  have hcoefficientNonneg : 0 ≤ coefficient :=
    bkRpowCoefficient_nonneg hbeta hc0 hc1
  have hrootBound := bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
    G d vertices.card vertices.card beta c hbeta hc0 hc1 hd hvertices le_rfl hprofile
  have hremainderRecurrence :
      (partition.remainder.card : ℝ) ≤
        (bkSumPreservingRecurrence G d vertices.card : ℝ) := by
    exact_mod_cast partition.remainder_card_le_bkSumPreservingRecurrence
  have hremainderBound :
      (partition.remainder.card : ℝ) ≤
        coefficient * vertices.card / denominator := by
    exact hremainderRecurrence.trans hrootBound
  have hremainderLeRoot : partition.remainder.card ≤ vertices.card :=
    Finset.card_le_card partition.remainder_subset
  have hseparatorRecurrence :
      (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤
        (bkSumPreservingRecurrence G d partition.remainder.card : ℝ) := by
    exact_mod_cast bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
      G d partition.remainder
  by_cases hterminal : bkScaleTerminal d partition.remainder.card
  · have hrecurrenceZero := bkSumPreservingRecurrence_eq_zero_of_terminal
      G d partition.remainder.card hterminal
    rw [hrecurrenceZero] at hseparatorRecurrence
    have hseparatorZero :
        (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤ 0 := by
      simpa only [Nat.cast_zero] using hseparatorRecurrence
    have hrightNonneg : 0 ≤
        (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * vertices.card /
          (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by positivity
    exact hseparatorZero.trans hrightNonneg
  · have hdremainder : d ≤ partition.remainder.card := by
      unfold bkScaleTerminal at hterminal
      omega
    have hsecondBound := bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
      G d vertices.card partition.remainder.card beta c hbeta hc0 hc1 hd
        hdremainder hremainderLeRoot hprofile
    have hscaledRemainder :
        coefficient * (partition.remainder.card : ℝ) / denominator ≤
          coefficient * (coefficient * vertices.card / denominator) / denominator := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hremainderBound hcoefficientNonneg)
        hdenominatorPos.le
    calc
      (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤
          (bkSumPreservingRecurrence G d partition.remainder.card : ℝ) :=
        hseparatorRecurrence
      _ ≤ coefficient * partition.remainder.card / denominator := hsecondBound
      _ ≤ coefficient * (coefficient * vertices.card / denominator) / denominator :=
        hscaledRemainder
      _ = (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * vertices.card /
          (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by
        simp only [coefficient, denominator]
        ring
end BKRecursivePartition
end QEC.Locality
