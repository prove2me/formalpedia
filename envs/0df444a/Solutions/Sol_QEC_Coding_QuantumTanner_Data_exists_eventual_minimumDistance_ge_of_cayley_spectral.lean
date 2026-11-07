-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.exists_eventual_minimumDistance_ge_of_cayley_spectral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:32:17.930802+00:00
-- url     : https://prove2.me/submissions/78293254-91ec-441b-a839-0e5d954f51a2

import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_eventual_minimumDistance_ge_of_mixing
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_mixing_of_cayley_bilinear_bounds
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
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square XBasis ZBasis : Type v)
        [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
        [Fintype XBasis] [Fintype ZBasis],
      ∀ (D : Data G A B Square XBasis ZBasis), D.complex.HasCayleyLinkIdentities →
      ∀ (dA dB dADual dBDual : Nat),
      MinimumDistance D.codeA dA → MinimumDistance D.codeB dB →
      MinimumDistance D.codeA.dual dADual → MinimumDistance D.codeB.dual dBDual →
      delta * Delta ≤ (dA : ℝ) → delta * Delta ≤ (dB : ℝ) →
      delta * Delta ≤ (dADual : ℝ) → delta * Delta ≤ (dBDual : ℝ) →
      Fintype.card A = Delta → Fintype.card B = Delta →
      IsRobust D.codeA D.codeB (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobust D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobustWithPunctureResistance D.codeA D.codeB
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      IsRobustWithPunctureResistance D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      HasMeanZeroBilinearBound D.complex.leftCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      HasMeanZeroBilinearBound D.complex.rightCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      ∀ distance : Nat, AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode distance →
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤ (distance : ℝ) := by
  obtain ⟨t, ht⟩ := exists_eventual_minimumDistance_ge_of_mixing
    delta epsilon gamma hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  refine ⟨t, ?_⟩
  intro Delta hDegree G A B Square XBasis ZBasis _ _ _ _ _ _ _ D hX dA dB dADual dBDual hA hB hADual hBDual
    hDistanceA hDistanceB hDistanceADual hDistanceBDual hCardA hCardB
    hRobust hRobustDual hPunctures hPuncturesDual hLeft hRight distance hmin
  obtain ⟨hSquare, hUnion⟩ := D.complex.mixing_of_cayley_bilinear_bounds hX
    (2 * Real.sqrt (Delta : ℝ)) (2 * Real.sqrt (Delta : ℝ)) (by positivity) (by positivity) hLeft hRight
  have hProduct : (2 * Real.sqrt (Delta : ℝ)) * (2 * Real.sqrt (Delta : ℝ)) =
      4 * (Delta : ℝ) := by nlinarith only [Real.sq_sqrt (Nat.cast_nonneg Delta)]
  have hSum : 2 * Real.sqrt (Delta : ℝ) + 2 * Real.sqrt (Delta : ℝ) =
      4 * Real.sqrt (Delta : ℝ) := by ring
  apply ht Delta hDegree G A B Square XBasis ZBasis D hX dA dB dADual dBDual hA hB hADual hBDual
    hDistanceA hDistanceB hDistanceADual hDistanceBDual hCardA hCardB
    hRobust hRobustDual hPunctures hPuncturesDual ?_ ?_ distance hmin
  · simpa only [hCardA, hCardB, hProduct] using hSquare
  · simpa only [hCardA, hCardB, hSum] using hUnion
end QEC.Coding.QuantumTanner.Data
