-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.why24OneRoundSyndromeProjector_apply_wordZ_encoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:06:32.42219+00:00
-- url     : https://prove2.me/submissions/3ed1a69e-11c6-4ce3-8421-466a495a3da1

import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRound_registerPairing_binaryLabelEquiv
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRound_wordXTransport_characterKet
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRound_wordZTransport_characterKet
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRound_wordXTransport_encoded
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_phase_eq_one_iff
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024Why24OddZSyndrome_eq_zero_iff
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
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
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_partialTraceRightRaw_mapDensity_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_symm_at
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
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
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.agWordStar_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
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
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
attribute [local simp] QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_symm_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
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
attribute [local simp] QEC.Semantics.traceNorm_neg


section
noncomputable section
namespace QEC.Distillation.Why24OneRoundProtocol
open QEC.Coding
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open QEC.Distillation
open QEC.Distillation.Why24AGFamily
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
open QEC.Semantics
open scoped BigOperators ComplexOrder
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
namespace Why24CCZFaultOperation
variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {fault : Finset Location}
end Why24CCZFaultOperation
namespace Why24LocalStochasticPreparation
variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {ideal : DensityOperator (Why24CCZRegister Location)}
end Why24LocalStochasticPreparation
open QEC.Distillation.OneQubitMagic
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
private theorem why24OneRound_exists_stabilizer_pairing_ne_zero
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (word : Why24Word Site)
    (hword : word ∉ R.stabilizerCode.dual.carrier) :
    ∃ shift : R.StabilizerCarrier,
      registerPairing 2
        (why24OneRoundBinaryLabelEquiv word)
        (why24OneRoundBinaryLabelEquiv shift.1) ≠ 0 := by
  have hnotOrthogonal : ¬ ∀ codeword : Why24Word Site,
      codeword ∈ R.stabilizerCode.carrier →
        wordPairing word codeword = 0 := by
    intro horthogonal
    exact hword ((R.stabilizerCode.mem_dual word).mpr horthogonal)
  rcases not_forall.mp hnotOrthogonal with ⟨codeword, hcodeword⟩
  have hcodeword' : codeword ∈ R.stabilizerCode.carrier ∧
      wordPairing word codeword ≠ 0 := Classical.not_imp.mp hcodeword
  obtain ⟨traceOne, htraceOne⟩ :=
    (Algebra.trace_surjective (ZMod 2) F1024) (1 : ZMod 2)
  let pairing := wordPairing word codeword
  let scalar := traceOne * pairing⁻¹
  let shift : R.StabilizerCarrier :=
    ⟨scalar • codeword,
      R.stabilizerCode.carrier.smul_mem scalar hcodeword'.1⟩
  refine ⟨shift, ?_⟩
  rw [why24OneRound_registerPairing_binaryLabelEquiv]
  have hpairing : wordPairing word shift.1 = traceOne := by
    change wordPairing word (scalar • codeword) = traceOne
    rw [map_smul]
    change scalar * wordPairing word codeword = traceOne
    dsimp only [scalar, pairing]
    rw [mul_assoc, inv_mul_cancel₀ hcodeword'.2, mul_one]
  rw [hpairing, htraceOne]
  exact one_ne_zero
private theorem why24OneRoundCharacterKet_inner_encoded_eq_zero_of_not_mem_dual
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (word : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Logical)
    (hword : word ∉ R.stabilizerCode.dual.carrier) :
    inner Complex (why24OneRoundCharacterKet word)
      (R.encodedCode.encode psi) = 0 := by
  obtain ⟨shift, hpairing⟩ :=
    why24OneRound_exists_stabilizer_pairing_ne_zero R word hword
  have hphase : phase 2 (registerPairing 2
      (why24OneRoundBinaryLabelEquiv word)
      (why24OneRoundBinaryLabelEquiv shift.1)) ≠ 1 := by
    intro hphase
    exact hpairing ((phase_eq_one_iff 2 _).mp hphase)
  have hunit := (wordXTransport shift.1).map_inner
    (R.encodedCode.encode psi) (why24OneRoundCharacterKet word)
  rw [why24OneRound_wordXTransport_encoded,
    why24OneRound_wordXTransport_characterKet] at hunit
  have heigen : phase 2 (registerPairing 2
      (why24OneRoundBinaryLabelEquiv word)
      (why24OneRoundBinaryLabelEquiv shift.1)) *
        inner Complex (R.encodedCode.encode psi)
          (why24OneRoundCharacterKet word) =
      inner Complex (R.encodedCode.encode psi)
        (why24OneRoundCharacterKet word) := by
    simpa only [inner_smul_right] using hunit
  have hzeroRight : inner Complex (R.encodedCode.encode psi)
      (why24OneRoundCharacterKet word) = 0 := by
    apply (mul_eq_zero.mp (show
      (phase 2 (registerPairing 2
          (why24OneRoundBinaryLabelEquiv word)
          (why24OneRoundBinaryLabelEquiv shift.1)) - 1) *
        inner Complex (R.encodedCode.encode psi)
          (why24OneRoundCharacterKet word) = 0 by
      rw [sub_mul, one_mul, heigen, sub_self])).resolve_left
    exact sub_ne_zero.mpr hphase
  calc
    inner Complex (why24OneRoundCharacterKet word)
        (R.encodedCode.encode psi) =
      starRingEnd Complex (inner Complex (R.encodedCode.encode psi)
        (why24OneRoundCharacterKet word)) :=
      (inner_conj_symm (why24OneRoundCharacterKet word)
        (R.encodedCode.encode psi)).symm
    _ = 0 := by rw [hzeroRight, map_zero]
private theorem why24OneRound_wordZTransport_self_inverse {Site : Type}
    [Fintype Site] [DecidableEq Site]
    (error : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Site) :
    wordZTransport error (wordZTransport error psi) = psi := by
  ext label
  simp only [wordZTransport_apply, wordZAmplitude]
  rw [← mul_assoc, tracePhase_square, one_mul]
private theorem why24OneRoundCharacterKet_inner_wordZ_encoded
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (error word : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Logical) :
    inner Complex (why24OneRoundCharacterKet word)
        (wordZTransport error (R.encodedCode.encode psi)) =
      inner Complex (why24OneRoundCharacterKet (word + error))
        (R.encodedCode.encode psi) := by
  have hunit := (wordZTransport error).map_inner
    (wordZTransport error (why24OneRoundCharacterKet word))
    (R.encodedCode.encode psi)
  rw [why24OneRound_wordZTransport_self_inverse,
    why24OneRound_wordZTransport_characterKet] at hunit
  exact hunit
private theorem why24OneRoundZSyndrome_add_self_zero (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    syndrome + syndrome = 0 := by
  have htwo : (2 : F1024) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  calc
    syndrome + syndrome =
        (1 : F1024) • syndrome + (1 : F1024) • syndrome := by simp
    _ = ((1 : F1024) + 1) • syndrome := (add_smul _ _ _).symm
    _ = (2 : F1024) • syndrome := by norm_num
    _ = 0 := by rw [htwo, zero_smul]
private theorem why24OneRoundZSyndromeMap_add_eq_zero_iff (r : Nat)
    (left right : Why24Word (f1024Why24OddPhysicalSite r)) :
    f1024Why24OddZSyndromeMap r (left + right) = 0 ↔
      f1024Why24OddZSyndromeMap r left =
        f1024Why24OddZSyndromeMap r right := by
  rw [why24OneRoundZSyndromeMap_add]
  constructor
  · intro hzero
    have h := congrArg
      (fun syndrome => syndrome + f1024Why24OddZSyndromeMap r right) hzero
    simpa only [add_assoc,
      why24OneRoundZSyndrome_add_self_zero, add_zero, zero_add] using h
  · intro heq
    rw [heq, why24OneRoundZSyndrome_add_self_zero]
private theorem why24OneRoundCharacterKet_inner_wordZ_encoded_eq_zero_of_ne
    (r : Nat)
    (error word : Why24Word (f1024Why24OddPhysicalSite r))
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r))
    (hsyndrome : f1024Why24OddZSyndromeMap r word ≠
      f1024Why24OddZSyndromeMap r error) :
    inner Complex (why24OneRoundCharacterKet word)
      (wordZTransport error
        ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) = 0 := by
  rw [why24OneRoundCharacterKet_inner_wordZ_encoded]
  apply why24OneRoundCharacterKet_inner_encoded_eq_zero_of_not_mem_dual
  intro hmem
  apply hsyndrome
  exact (why24OneRoundZSyndromeMap_add_eq_zero_iff r word error).mp
    ((f1024Why24OddZSyndrome_eq_zero_iff r (word + error)).mpr hmem)
private theorem why24OneRoundSyndromeProjector_apply_wordZ_encoded_eq_zero_of_ne
    (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r))
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r))
    (syndrome : f1024Why24OddZSyndrome r)
    (hsyndrome : syndrome ≠ f1024Why24OddZSyndromeMap r error) :
    why24OneRoundSyndromeProjector r syndrome
        (wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) = 0 := by
  unfold why24OneRoundSyndromeProjector
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro word _
  by_cases hsector : f1024Why24OddZSyndromeMap r word = syndrome
  · rw [if_pos hsector]
    simp only [InnerProductSpace.toLinearMap_rankOne,
      LinearMap.smulRight_apply, innerₛₗ_apply_apply]
    have hword : f1024Why24OddZSyndromeMap r word ≠
        f1024Why24OddZSyndromeMap r error := by
      intro heq
      exact hsyndrome (hsector.symm.trans heq)
    rw [why24OneRoundCharacterKet_inner_wordZ_encoded_eq_zero_of_ne
      r error word psi hword, zero_smul]
  · simp [hsector]
namespace Why24OneRoundTwirledConversionLaw
variable {r : Nat}
variable {preparation : Why24LocalStochasticPreparation
  (Fin (why24OneRoundInputCount r))
  (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
end Why24OneRoundTwirledConversionLaw
end QEC.Distillation.Why24OneRoundProtocol
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24OneRoundProtocol
open QEC.Coding
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open QEC.Distillation
open QEC.Distillation.Why24AGFamily
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
open QEC.Semantics
open scoped BigOperators ComplexOrder
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
open QEC.Distillation.OneQubitMagic
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
namespace QEC.Distillation.Why24OneRoundProtocol
theorem _root_.solution
    (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r))
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r))
    (syndrome : f1024Why24OddZSyndrome r) :
    why24OneRoundSyndromeProjector r syndrome
        (wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) =
      if syndrome = f1024Why24OddZSyndromeMap r error then
        wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)
      else 0 := by
  by_cases hsyndrome : syndrome = f1024Why24OddZSyndromeMap r error
  · subst syndrome
    rw [if_pos rfl]
    calc
      why24OneRoundSyndromeProjector r
          (f1024Why24OddZSyndromeMap r error)
          (wordZTransport error
            ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) =
          (∑ measured : f1024Why24OddZSyndrome r,
            why24OneRoundSyndromeProjector r measured)
            (wordZTransport error
              ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) := by
        rw [LinearMap.sum_apply, Finset.sum_eq_single
          (f1024Why24OddZSyndromeMap r error)]
        · intro other _ hother
          exact
            why24OneRoundSyndromeProjector_apply_wordZ_encoded_eq_zero_of_ne
              r error psi other hother
        · simp
      _ = wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi) := by
        rw [why24OneRound_sum_syndromeProjector_eq_one]
        rfl
  · rw [if_neg hsyndrome]
    exact
      why24OneRoundSyndromeProjector_apply_wordZ_encoded_eq_zero_of_ne
        r error psi syndrome hsyndrome
end QEC.Distillation.Why24OneRoundProtocol
