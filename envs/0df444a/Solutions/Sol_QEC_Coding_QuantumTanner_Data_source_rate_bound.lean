-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.source_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:18:49.746846+00:00
-- url     : https://prove2.me/submissions/d651b48c-1254-45fb-b0cb-4720e6cb5681

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_le_encodedDimension_add_checks
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Dimension_tensorCode
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_card_group_mul_local_degree_eq_twice_card_square
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_card_xBasis_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_RawData_card_zBasis_eq
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
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
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
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
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.Data
open Classical
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis) (Delta r : Nat) (rho : ℝ)
    (hDelta : 0 < Delta) (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta) (hRho : 0 ≤ rho) (hRhoHalf : rho < 1 / 2)
    (hRate : (r : ℝ) ≤ rho * Delta)
    (hCodeA : Dimension D.codeA = r) (hCodeB : Dimension D.codeB = Delta - r) :
    (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) := by
  have hX : Fintype.card XBasis = (Delta - r) * r := by
    rw [D.toRawData.card_xBasis_eq, Dimension_tensorCode,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      Length, Length, hA, hB, hCodeA, hCodeB, Nat.sub_sub_self hr]
  have hZ : Fintype.card ZBasis = r * (Delta - r) := by
    rw [D.toRawData.card_zBasis_eq, Dimension_tensorCode, hCodeA, hCodeB]
  have hChecks := D.blockLength_le_encodedDimension_add_checks
  rw [hX, hZ] at hChecks
  have hChecksReal : (D.blockLength : ℝ) ≤ D.encodedDimension +
      (Fintype.card G : ℝ) * (((Delta - r : Nat) : ℝ) * r + r * ((Delta - r : Nat) : ℝ)) := by
    exact_mod_cast hChecks
  have hCard := D.complex.card_group_mul_local_degree_eq_twice_card_square
  rw [hA, hB] at hCard
  have hCardNat : Fintype.card G * Delta * Delta = 2 * D.blockLength := by
    simpa only [Data.blockLength, mul_assoc] using hCard
  have hCardReal : (Fintype.card G : ℝ) * Delta * Delta = 2 * D.blockLength := by
    exact_mod_cast hCardNat
  have hSub : ((Delta - r : Nat) : ℝ) = (Delta : ℝ) - r := by
    exact Nat.cast_sub hr
  rw [hSub] at hChecksReal
  have hDeltaReal : 0 < (Delta : ℝ) := by exact_mod_cast hDelta
  have hMargin : 0 ≤ (Delta : ℝ) - rho * Delta - r := by nlinarith
  have hProduct := mul_nonneg (sub_nonneg.mpr hRate) hMargin
  have hLocal : 4 * (r : ℝ) * (Delta - r) ≤
      4 * rho * (1 - rho) * (Delta : ℝ) ^ 2 := by nlinarith only [hProduct]
  have hGlobal := mul_le_mul_of_nonneg_left hLocal
    (show 0 ≤ (Fintype.card G : ℝ) / 2 by positivity)
  nlinarith only [hChecksReal, hCardReal, hGlobal]
end QEC.Coding.QuantumTanner.Data
