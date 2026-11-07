-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticPSLFamily.exists_eventual_sample_of_spectral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:49:56.405125+00:00
-- url     : https://prove2.me/submissions/c8a43453-1195-427e-80ed-a47d41c3e369

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_toPGL_liftToPSL
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveMatrixEquiv_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_toPGL_pslLeft
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_toPGL_pslRight
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_cofinal_group_card
import Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_index_card
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_good_sample_family
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
attribute [local simp] QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mk
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.toPGL_pslLeft
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.toPGL_pslRight
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit
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
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion
variable (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
  (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
theorem _root_.solution
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : ℕ, ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → t ≤ p + 1 →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho (p + 1))
        (TorusIndex epsilon) (TorusIndex epsilon),
      (∀ n, HasMeanZeroBilinearBound
        (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      (∀ n, HasMeanZeroBilinearBound
        (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
        (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
        (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
        (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
        (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1) sample := by
  let gamma : ℝ := 3 / 4 + eta / 2
  have hGammaLower : 1 / 2 + eta < gamma := by dsimp [gamma]; linarith
  have hGammaUpper : gamma < 1 := by dsimp [gamma]; linarith
  obtain ⟨t, ht⟩ := exists_eventual_good_sample_family
    delta eta gamma rho hDelta hDeltaHalf hEta hEtaHalf
    hGammaLower hGammaUpper hRho hRhoHalf hEntropy
  refine ⟨t, ?_⟩
  intro p _ hOdd epsilon hEpsilon hNonSquare hLarge
  have hCard := index_card p hOdd epsilon hNonSquare
  obtain ⟨sample, hSample⟩ := ht (p + 1) hLarge
    (TorusIndex epsilon) (TorusIndex epsilon) hCard hCard
  refine ⟨sample, ?_⟩
  intro hLeft hRight
  exact @hSample ℕ (fun n => GroupAt p n)
    (fun _ => inferInstance) (fun n => groupAtFintype p n) (left p hOdd epsilon hEpsilon)
    (right p hOdd epsilon hEpsilon) (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
    (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
    (total_nonconjugacy p hOdd epsilon hEpsilon) hLeft hRight (cofinal_group_card p)
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily
