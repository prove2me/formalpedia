-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.why24OneRoundOutputError_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:21:37.448633+00:00
-- url     : https://prove2.me/submissions/5dd08089-c0c0-4aad-899e-102cfa59d9ab

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
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRoundSyndromeProjector_apply_wordZ_encoded
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRoundCorrection_restores_encoded
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRoundDecoderChannel_rankOne_encoded
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24CorrelatedPrepareInput_actual
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_why24OneRoundFailureMass_le
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
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_rawOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_finset_weighted_residual_traceNorm_le_two_mul_mass
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
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
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_traceNorm_eq_one
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_inducedMap_apply
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
import Theorems.Thm_QEC_Semantics_traceNorm_add_le
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
namespace Why24OneRoundTwirledConversionLaw
variable {r : Nat}
variable {preparation : Why24LocalStochasticPreparation
  (Fin (why24OneRoundInputCount r))
  (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
end Why24OneRoundTwirledConversionLaw
@[simp]
private theorem why24OneRoundWitnessLocations_card (r : Nat)
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) :
    (why24OneRoundWitnessLocations r sites gate).card = sites.card := by
  unfold why24OneRoundWitnessLocations
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro left _ right _ heq
    apply Subtype.ext
    exact (why24OneRoundPhysicalSiteEquiv r).injective
      (congrArg Prod.fst ((why24OneRoundCCZLocationEquiv r).injective heq))
private theorem why24OneRoundCorrectedErrorKet_eq_encoded_of_weight_le
    (r : Nat) (error : Why24Word (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    why24OneRoundCorrectedErrorKet r error =
      why24OneRoundEncodedIdealKet r := by
  unfold why24OneRoundCorrectedErrorKet why24OneRoundErrorKet
  exact why24OneRoundCorrection_restores_encoded r error
    (why24OneRoundLogicalIdealKet r) herror
private theorem why24OneRoundInstrument_inducedMap_errorDensity (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    (why24OneRoundInstrument r).kraus.inducedMap
        (why24OneRoundErrorDensity r error).toOperator =
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCorrectedErrorKet r error)
        (why24OneRoundCorrectedErrorKet r error)).toLinearMap := by
  rw [why24OneRoundErrorDensity, DensityOperator.pureDensity_toOperator]
  rw [why24OneRoundInstrument,
    FiniteInstrument.bind_inducedMap_apply]
  change
    (∑ syndrome : f1024Why24OddZSyndrome r,
      (why24OneRoundCorrectionInstrument r syndrome).kraus.inducedMap
        ((why24OneRoundSyndromeProjector r syndrome).comp
          ((InnerProductSpace.rankOne Complex
            (why24OneRoundErrorKet r error)
            (why24OneRoundErrorKet r error)).toLinearMap.comp
              (LinearMap.adjoint
                (why24OneRoundSyndromeProjector r syndrome))))) = _
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]
  simp only [FiniteKrausFamily.inducedMap_apply,
    why24OneRoundCorrectionInstrument, Fintype.sum_unique]
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]
  rw [Finset.sum_eq_single (f1024Why24OddZSyndromeMap r error)]
  · change
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCorrection r (f1024Why24OddZSyndromeMap r error)
          (why24OneRoundSyndromeProjector r
            (f1024Why24OddZSyndromeMap r error)
            (why24OneRoundErrorKet r error)))
        (why24OneRoundCorrection r (f1024Why24OddZSyndromeMap r error)
          (why24OneRoundSyndromeProjector r
            (f1024Why24OddZSyndromeMap r error)
            (why24OneRoundErrorKet r error)))).toLinearMap = _
    rfl
  · intro syndrome _ hsyndrome
    change
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCorrection r syndrome
          (why24OneRoundSyndromeProjector r syndrome
            (wordZTransport error
              ((f1024Why24OddWeightedMatrix r).encodedCode.encode
                (why24OneRoundLogicalIdealKet r)))))
        (why24OneRoundCorrection r syndrome
          (why24OneRoundSyndromeProjector r syndrome
            (wordZTransport error
              ((f1024Why24OddWeightedMatrix r).encodedCode.encode
                (why24OneRoundLogicalIdealKet r)))))).toLinearMap = 0
    rw [
      why24OneRoundSyndromeProjector_apply_wordZ_encoded,
      if_neg hsyndrome]
    change (InnerProductSpace.rankOne Complex
      ((why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap 0)
      ((why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap 0)).toLinearMap = 0
    rw [map_zero]
    apply LinearMap.ext
    intro vector
    simp only [InnerProductSpace.toLinearMap_rankOne,
      LinearMap.smulRight_apply, innerₛₗ_apply_apply, smul_zero,
      LinearMap.zero_apply]
  · simp
private theorem why24OneRoundDecodedErrorDensity_eq_ideal_of_weight_le
    (r : Nat) (error : Why24Word (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    why24OneRoundDecodedErrorDensity r error =
      why24OneRoundLogicalIdealDensity r := by
  apply DensityOperator.ext_toOperator
  rw [why24OneRoundDecodedErrorDensity, QuantumChannel.mapDensity_toOperator,
    why24OneRoundPhysicalChannel, QuantumChannel.comp_apply,
    FiniteKrausFamily.toQuantumChannel_apply,
    why24OneRoundInstrument_inducedMap_errorDensity,
    why24OneRoundCorrectedErrorKet_eq_encoded_of_weight_le r error herror,
    why24OneRoundEncodedIdealKet,
    why24OneRoundDecoderChannel_rankOne_encoded,
    why24OneRoundLogicalIdealDensity,
    DensityOperator.pureDensity_toOperator]
private theorem why24OneRoundRun_rawOutput_toOperator_eq_decodedErrorSum
    (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundRun r preparation).rawOutput.toOperator =
      ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        ((why24OneRoundDerivedTwirledConversionLaw r preparation).errorMass
          error : Complex) •
          (why24OneRoundDecodedErrorDensity r error).toOperator := by
  rw [why24OneRoundRun, DistillationRun.postprocess_rawOutput]
  change why24OneRoundDecoderChannel r
      (((why24OneRoundInstrument r).kraus.toQuantumChannel
        (why24OneRoundInstrument_complete r))
        (why24CorrelatedPrepareInput r preparation
          (why24LocalStochasticResourceInputs preparation)).toOperator) = _
  rw [why24CorrelatedPrepareInput_actual,
    why24OneRoundPreparedPhysicalDensity,
    why24OneRoundPreparedPhysicalDensityForLaw,
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  simp only [map_sum, map_smul, why24OneRoundDecodedErrorDensity,
    why24OneRoundPhysicalChannel, QuantumChannel.mapDensity_toOperator,
    QuantumChannel.comp_apply]
private theorem why24OneRoundFailureMass_eq_errorMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    why24OneRoundFailureMassForLaw r preparation law =
      ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        if f1024Why24OddDecodingRadius r < HammingWeight error then
          law.errorMass error
        else 0 := by
  unfold why24OneRoundFailureMassForLaw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro error _
  change
    (∑ fault : Finset (Fin (why24OneRoundInputCount r)),
      if f1024Why24OddDecodingRadius r < HammingWeight error then
        law.branchMass fault error
      else 0) =
    if f1024Why24OddDecodingRadius r < HammingWeight error then
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        law.branchMass fault error
    else 0
  by_cases herror : f1024Why24OddDecodingRadius r < HammingWeight error
  · simp_rw [if_pos herror]
  · simp_rw [if_neg herror]
    simp
private theorem why24OneRoundDecodedErrorDensity_traceNorm_sub_ideal_le_two
    (r : Nat) (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    traceNorm ((why24OneRoundDecodedErrorDensity r error).toOperator -
      (why24OneRoundLogicalIdealDensity r).toOperator) ≤ 2 := by
  calc
    traceNorm ((why24OneRoundDecodedErrorDensity r error).toOperator -
        (why24OneRoundLogicalIdealDensity r).toOperator) ≤
      traceNorm (why24OneRoundDecodedErrorDensity r error).toOperator +
        traceNorm (-(why24OneRoundLogicalIdealDensity r).toOperator) := by
      simpa [sub_eq_add_neg] using
        traceNorm_add_le
          (why24OneRoundDecodedErrorDensity r error).toOperator
          (-(why24OneRoundLogicalIdealDensity r).toOperator)
    _ = 2 := by
      rw [DensityOperator.traceNorm_eq_one, traceNorm_neg,
        DensityOperator.traceNorm_eq_one]
      norm_num
private theorem why24OneRoundRun_sub_ideal_eq_decodedResidual (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundRun r preparation).rawOutput.toOperator -
        (why24OneRoundLogicalIdealDensity r).toOperator =
      why24OneRoundDecodedResidual r
        (why24OneRoundDerivedTwirledConversionLaw r preparation) := by
  let law := why24OneRoundDerivedTwirledConversionLaw r preparation
  change (why24OneRoundRun r preparation).rawOutput.toOperator -
      (why24OneRoundLogicalIdealDensity r).toOperator =
    why24OneRoundDecodedResidual r law
  rw [why24OneRoundRun_rawOutput_toOperator_eq_decodedErrorSum]
  have hmass :
      (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
          (law.errorMass error : Complex)) = 1 := by
    rw [← Complex.ofReal_sum, law.errorMass_sum]
    exact Complex.ofReal_one
  calc
    (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        (law.errorMass error : Complex) •
          (why24OneRoundDecodedErrorDensity r error).toOperator) -
        (why24OneRoundLogicalIdealDensity r).toOperator =
      (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        (law.errorMass error : Complex) •
          (why24OneRoundDecodedErrorDensity r error).toOperator) -
        (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
          (law.errorMass error : Complex)) •
            (why24OneRoundLogicalIdealDensity r).toOperator := by
      rw [hmass, one_smul]
    _ = ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        ((law.errorMass error : Complex) •
            (why24OneRoundDecodedErrorDensity r error).toOperator -
          (law.errorMass error : Complex) •
            (why24OneRoundLogicalIdealDensity r).toOperator) := by
      rw [Finset.sum_smul, Finset.sum_sub_distrib]
    _ = why24OneRoundDecodedResidual r law := by
      unfold why24OneRoundDecodedResidual
      apply Finset.sum_congr rfl
      intro error _
      by_cases herror : f1024Why24OddDecodingRadius r < HammingWeight error
      · rw [if_pos herror]
        exact (smul_sub (law.errorMass error : Complex)
          (why24OneRoundDecodedErrorDensity r error).toOperator
          (why24OneRoundLogicalIdealDensity r).toOperator).symm
      · rw [if_neg herror,
          why24OneRoundDecodedErrorDensity_eq_ideal_of_weight_le r error
            (Nat.le_of_not_gt herror)]
        simp
private theorem why24OneRoundDecodedResidual_traceNorm_le_two_mul_failureMass
    (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    traceNorm (why24OneRoundDecodedResidual r law) ≤
      2 * why24OneRoundFailureMassForLaw r preparation law := by
  unfold why24OneRoundDecodedResidual
  calc
    traceNorm (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        if f1024Why24OddDecodingRadius r < HammingWeight error then
          (law.errorMass error : Complex) •
            ((why24OneRoundDecodedErrorDensity r error).toOperator -
              (why24OneRoundLogicalIdealDensity r).toOperator)
        else 0) ≤
      ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        if f1024Why24OddDecodingRadius r < HammingWeight error then
          2 * law.errorMass error
        else 0 := by
      simpa using
        (FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
          (Finset.univ : Finset
            (Why24Word (f1024Why24OddPhysicalSite r)))
          law.errorMass
          (fun error =>
            f1024Why24OddDecodingRadius r < HammingWeight error)
          (fun error => (why24OneRoundDecodedErrorDensity r error).toOperator)
          (why24OneRoundLogicalIdealDensity r).toOperator
          law.errorMass_nonneg
          (why24OneRoundDecodedErrorDensity_traceNorm_sub_ideal_le_two r))
    _ = 2 * why24OneRoundFailureMassForLaw r preparation law := by
      rw [why24OneRoundFailureMass_eq_errorMass]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro error _
      simp only [mul_ite, mul_zero]
private theorem why24OneRoundOutputError_le_failureMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    why24OneRoundOutputError r preparation ≤
      why24OneRoundFailureMass r preparation := by
  let law := why24OneRoundDerivedTwirledConversionLaw r preparation
  rw [why24OneRoundOutputError,
    why24OneRoundTraceDistance,
    why24OneRoundRun_sub_ideal_eq_decodedResidual,
    why24OneRoundFailureMass]
  calc
    (2 : Real)⁻¹ * traceNorm (why24OneRoundDecodedResidual r law) ≤
        (2 : Real)⁻¹ *
          (2 * why24OneRoundFailureMassForLaw r preparation law) :=
      mul_le_mul_of_nonneg_left
        (why24OneRoundDecodedResidual_traceNorm_le_two_mul_failureMass
          r preparation law) (by norm_num)
    _ = why24OneRoundFailureMassForLaw r preparation law := by ring
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
theorem _root_.solution (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    why24OneRoundOutputError r preparation ≤
      (Nat.choose (f1024Why24OddLength r)
        (f1024Why24OddDecodingRadius r + 1) : Real) *
        (70 * preparation.rate) ^
          (f1024Why24OddDecodingRadius r + 1) :=
  (why24OneRoundOutputError_le_failureMass r preparation).trans
    (why24OneRoundFailureMass_le r preparation)
end QEC.Distillation.Why24OneRoundProtocol
