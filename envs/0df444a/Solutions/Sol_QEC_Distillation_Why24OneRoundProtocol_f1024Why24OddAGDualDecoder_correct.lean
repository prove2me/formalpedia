-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.f1024Why24OddAGDualDecoder_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:49.095726+00:00
-- url     : https://prove2.me/submissions/77f8df56-d51a-4c1d-9058-45dd09e44b6e

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
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_f1024Why24OddDecoderAuxiliaryDivisor_degree
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_f1024Why24OddDecoderAuxiliary_dimension_gt_radius
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_eq_bot_of_negative_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluationLinearMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dual_distance_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZeroOn_mem_riemannRochSubmodule_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_zeroCoordinateDivisor_degree_eq_card
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_le_of
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
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024Why24OddLength_bounds
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024Why24OddStabilizerCode_dual_distance_lower_bound
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
private theorem why24Decoder_evaluationRegularityOfMem (r : Nat)
    (D : Divisor (GlobalPlace F1024 (F1024TowerLevel (2 * r + 2))))
    (hD : forall site : f1024Why24OddPhysicalSite r,
      D (f1024Why24OddPhysicalRationalPlace r site).place = 0)
    (function : GlobalPlace.riemannRochSubmodule D)
    (site : f1024Why24OddPhysicalSite r) :
    GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place
      (function : F1024TowerLevel (2 * r + 2)) := by
  have hbound :=
    (GlobalPlace.mem_riemannRochSubmodule_iff D
      (function : F1024TowerLevel (2 * r + 2))).mp
        function.property (f1024Why24OddPhysicalRationalPlace r site).place
  rw [hD site] at hbound
  simpa [GlobalPlace.RegularAt] using hbound
private theorem why24Decoder_evaluateRegular_mul (r : Nat)
    (site : f1024Why24OddPhysicalSite r)
    (left right : F1024TowerLevel (2 * r + 2))
    (hleft : GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place left)
    (hright : GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place right)
    (hproduct : GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place (left * right)) :
    (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
        (left * right) hproduct =
      (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular left hleft *
        (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular right hright := by
  let xleft : GlobalPlace.valuationRing
      (f1024Why24OddPhysicalRationalPlace r site).place :=
    ⟨left, (GlobalPlace.mem_valuationRing_iff _ left).mpr hleft⟩
  let xright : GlobalPlace.valuationRing
      (f1024Why24OddPhysicalRationalPlace r site).place :=
    ⟨right, (GlobalPlace.mem_valuationRing_iff _ right).mpr hright⟩
  let xproduct : GlobalPlace.valuationRing
      (f1024Why24OddPhysicalRationalPlace r site).place :=
    ⟨left * right, (GlobalPlace.mem_valuationRing_iff _ _).mpr hproduct⟩
  change (f1024Why24OddPhysicalRationalPlace r site).evaluate xproduct =
    (f1024Why24OddPhysicalRationalPlace r site).evaluate xleft *
      (f1024Why24OddPhysicalRationalPlace r site).evaluate xright
  have hmul : xproduct = xleft * xright := by
    rfl
  rw [hmul]
  exact (f1024Why24OddPhysicalRationalPlace r site).evaluate.map_mul _ _
private theorem why24DecoderScaledEvaluation_mul_apply (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (row : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r))
    (site : f1024Why24OddPhysicalSite r) :
    why24DecoderScaledEvaluationLinearMap r
        (why24DecoderMultiplyIntoShortened r row locator) site =
      f1024Why24OddCoordinateWeight r site.1 *
        (agEvaluationLinearMap
            (f1024Why24OddDecoderAuxiliaryDivisor r)
            (f1024Why24OddPhysicalRationalPlace r)
            (f1024Why24OddDecoderAuxiliary_disjoint r) locator site *
          agEvaluationLinearMap
            (f1024Why24OddDecoderComplementDivisor r)
            (f1024Why24OddPhysicalRationalPlace r)
            (why24DecoderComplementDivisor_apply_physical r) row site) := by
  unfold why24DecoderScaledEvaluationLinearMap
  simp only [agEvaluationLinearMap_apply]
  change f1024Why24OddCoordinateWeight r site.1 *
      (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
        ((locator : F1024TowerLevel (2 * r + 2)) * row) _ =
    f1024Why24OddCoordinateWeight r site.1 *
      ((f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
          (locator : F1024TowerLevel (2 * r + 2)) _ *
        (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
          (row : F1024TowerLevel (2 * r + 2)) _)
  congr 1
  exact why24Decoder_evaluateRegular_mul r site
    (locator : F1024TowerLevel (2 * r + 2))
    (row : F1024TowerLevel (2 * r + 2))
    (why24Decoder_evaluationRegularityOfMem r
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site)
    (why24Decoder_evaluationRegularityOfMem r
      (f1024Why24OddDecoderComplementDivisor r)
      (why24DecoderComplementDivisor_apply_physical r) row site)
    (why24Decoder_evaluationRegularityOfMem r
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (why24DecoderShortenedDivisor_apply_physical r)
      (why24DecoderMultiplyIntoShortened r row locator) site)
private theorem why24DecoderAuxiliarySupportEvaluation_finrank (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r)) :
    Module.finrank F1024 ({site // site ∈ hammingSupport error} → F1024) =
      HammingWeight error := by
  rw [HammingWeight_eq_card_hammingSupport, Module.finrank_pi]
  simp
private theorem why24DecoderAuxiliarySupportEvaluation_kernel_ne_bot (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    LinearMap.ker (why24DecoderAuxiliarySupportEvaluation r error) ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  rw [why24DecoderAuxiliarySupportEvaluation_finrank]
  exact herror.trans_lt
    (f1024Why24OddDecoderAuxiliary_dimension_gt_radius r)
private theorem why24DecoderSupportLocator_mem_linearSystem_kernel (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ∈
      LinearMap.ker (why24DecoderAuxiliarySupportEvaluation r error)) :
    locator ∈ LinearMap.ker
      (f1024Why24OddDecoderLinearSystem r
        (f1024Why24OddZSyndromeMap r error)) := by
  rw [LinearMap.mem_ker] at hlocator ⊢
  funext equation
  simp only [f1024Why24OddDecoderLinearSystem, LinearMap.pi_apply,
    LinearMap.comp_apply, why24DecoderSyndromePairing_mk,
    wordPairing_apply]
  apply Finset.sum_eq_zero
  intro site _
  by_cases hsite : site ∈ hammingSupport error
  · have hzero := congrFun hlocator ⟨site, hsite⟩
    change agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0 at hzero
    change error site * why24DecoderScaledEvaluationLinearMap r
      (why24DecoderMultiplyIntoShortened r
        (Module.finBasis F1024
          (GlobalPlace.riemannRochSubmodule
            (f1024Why24OddDecoderComplementDivisor r)) equation) locator) site = 0
    rw [why24DecoderScaledEvaluation_mul_apply]
    change error site *
      (f1024Why24OddCoordinateWeight r site.1 *
        (agEvaluationLinearMap
            (f1024Why24OddDecoderAuxiliaryDivisor r)
            (f1024Why24OddPhysicalRationalPlace r)
            (f1024Why24OddDecoderAuxiliary_disjoint r) locator site * _)) = 0
    rw [hzero]
    ring
  · have herrorZero : error site = 0 := by
      simpa [hammingSupport] using hsite
    rw [herrorZero, zero_mul]
private theorem why24DecoderLinearSystem_kernel_ne_bot_of_error (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    LinearMap.ker
        (f1024Why24OddDecoderLinearSystem r
          (f1024Why24OddZSyndromeMap r error)) ≠ ⊥ := by
  have hsupport : LinearMap.ker
      (why24DecoderAuxiliarySupportEvaluation r error) ≠ ⊥ :=
    why24DecoderAuxiliarySupportEvaluation_kernel_ne_bot r error herror
  have hle : LinearMap.ker
      (why24DecoderAuxiliarySupportEvaluation r error) ≤
        LinearMap.ker
          (f1024Why24OddDecoderLinearSystem r
            (f1024Why24OddZSyndromeMap r error)) := by
    intro locator hlocator
    exact why24DecoderSupportLocator_mem_linearSystem_kernel r error
      locator hlocator
  intro hbot
  rw [hbot] at hle
  apply hsupport
  exact le_antisymm hle bot_le
private theorem why24DecoderLinearSystem_kernel_finrank_pos_of_error (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    0 < Module.finrank F1024
      (LinearMap.ker
        (f1024Why24OddDecoderLinearSystem r
          (f1024Why24OddZSyndromeMap r error))) := by
  exact (Submodule.one_le_finrank_iff.mpr
    (why24DecoderLinearSystem_kernel_ne_bot_of_error r error herror))
private theorem why24DecoderLocator_mem_kernel (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    why24DecoderLocator r syndrome ∈
      LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome) := by
  letI : Module.Free F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :=
    Module.Free.of_divisionRing F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
  unfold why24DecoderLocator
  split_ifs with hdimension
  · exact (Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
      ⟨0, hdimension⟩).2
  · exact (LinearMap.ker _).zero_mem
private theorem why24DecoderLocator_ne_zero_of_finrank_pos (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (hdimension : 0 < Module.finrank F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))) :
    why24DecoderLocator r syndrome ≠ 0 := by
  letI : Module.Free F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :=
    Module.Free.of_divisionRing F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
  rw [why24DecoderLocator, dif_pos hdimension]
  intro hzero
  have hbasis : Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
      ⟨0, hdimension⟩ ≠ 0 :=
    (Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))).ne_zero
      ⟨0, hdimension⟩
  apply hbasis
  apply Subtype.ext
  exact hzero
private theorem why24DecoderLocator_ne_zero_of_error (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    why24DecoderLocator r (f1024Why24OddZSyndromeMap r error) ≠ 0 :=
  why24DecoderLocator_ne_zero_of_finrank_pos r _
    (why24DecoderLinearSystem_kernel_finrank_pos_of_error r error herror)
private theorem why24DecoderOddGenus_subtrahend_le (r : Nat) :
    34 * 32 ^ (r + 1) ≤ 33 * 32 ^ (2 * r + 2) := by
  let q := 32 ^ (r + 1)
  have hpower : 32 ≤ q := by
    dsimp only [q]
    have h := pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hbig : 32 ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  change 34 * q ≤ 33 * 32 ^ (2 * r + 2)
  rw [hbig]
  have hmul : q * 32 ≤ q * q := Nat.mul_le_mul_left q hpower
  nlinarith
private theorem why24DecoderOddGenus_cast (r : Nat) :
    (oddGenus r : Int) =
      33 * (32 : Int) ^ (2 * r + 2) -
        34 * (32 : Int) ^ (r + 1) + 1 := by
  rw [oddGenus, Nat.cast_add,
    Nat.cast_sub (why24DecoderOddGenus_subtrahend_le r)]
  norm_num
private theorem why24DecoderOddGenus_lower_bound (r : Nat) :
    32705 ≤ oddGenus r := by
  let q : Int := (32 : Int) ^ (r + 1)
  have hqNat : 32 ≤ 32 ^ (r + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hq : (32 : Int) ≤ q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hpower : (32 : Int) ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  have hcast := why24DecoderOddGenus_cast r
  have hbound : (32705 : Int) ≤ (oddGenus r : Int) := by
    rw [hcast, hpower]
    nlinarith
  exact_mod_cast hbound
private theorem why24DecoderOddGenus_mod_eight (r : Nat) :
    oddGenus r % 8 = 1 := by
  have hlarge := why24DecoderOddGenus_subtrahend_le r
  have hhigh : 32 ^ (2 * r + 2) % 8 = 0 := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ]
    omega
  have hlow : 32 ^ (r + 1) % 8 = 0 := by
    rw [pow_succ]
    omega
  unfold oddGenus
  omega
private theorem why24DecoderPhysicalRationalPlace_injective (r : Nat) :
    Function.Injective
      (fun site => (f1024Why24OddPhysicalRationalPlace r site).place) := by
  intro left right heq
  apply Subtype.ext
  exact f1024Why24OddRetainedRationalPlace_injective r heq
private theorem why24DecoderComplementDivisor_degree (r : Nat) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderComplementDivisor r) =
      (selectedDivisorDegree (oddGenus r) : Int) -
        selectedLogicalCount (oddGenus r) -
          selectedAuxiliaryDegree (oddGenus r) := by
  rw [f1024Why24OddDecoderComplementDivisor,
    Divisor.degree_sub, Divisor.degree_sub,
    f1024Why24OddADivisor_degree,
    f1024Why24OddPivotDivisor_degree,
    f1024Why24OddDecoderAuxiliaryDivisor_degree]
private theorem why24DecoderComplementDivisor_largeDegree (r : Nat) :
    2 * (GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : Int) - 1 ≤
      Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderComplementDivisor r) := by
  rw [f1024TowerLevel_functionFieldGenus_even,
    why24DecoderComplementDivisor_degree]
  have hmod := why24DecoderOddGenus_mod_eight r
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount,
    selectedAuxiliaryDegree]
  omega
private theorem why24DecoderComplementDivisor_degree_lt_physicalCard
    (r : Nat) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderComplementDivisor r) <
      Fintype.card (f1024Why24OddPhysicalSite r) := by
  rw [why24DecoderComplementDivisor_degree]
  have hlower := (f1024Why24OddLength_bounds r).1
  rw [f1024Why24OddLength] at hlower
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount,
    selectedAuxiliaryDegree, selectedPhysicalLengthLowerBound] at hlower ⊢
  omega
private theorem why24DecoderComplementDesignedDistance (r : Nat) :
    Int.toNat
        (((selectedDivisorDegree (oddGenus r) : Int) -
              selectedLogicalCount (oddGenus r) -
                selectedAuxiliaryDegree (oddGenus r)) + 2 -
          2 * (oddGenus r : Int)) =
      selectedDecodingRadius (oddGenus r) + 2 := by
  have hmod := why24DecoderOddGenus_mod_eight r
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount,
    selectedAuxiliaryDegree, selectedDecodingRadius]
  omega
private theorem why24DecoderComplementAGCode_dual_distance_lower_bound
    (r : Nat) :
    (f1024Why24OddDecodingRadius r + 2 : WithTop Nat) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
        (why24DecoderComplementAGCode r).dual := by
  have h := agEvaluation_dual_distance_lower_bound
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddDecoderComplementDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderPhysicalRationalPlace_injective r)
    (why24DecoderComplementDivisor_apply_physical r)
    (why24DecoderComplementDivisor_largeDegree r)
    (why24DecoderComplementDivisor_degree_lt_physicalCard r)
  change (Int.toNat
      (Divisor.degree (GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
          (f1024Why24OddDecoderComplementDivisor r) + 2 -
        2 * (GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : Int)) : WithTop Nat) ≤
    QEC.Coding.HypergraphProduct.extendedMinimumDistance
      (why24DecoderComplementAGCode r).dual at h
  rw [why24DecoderComplementDivisor_degree,
    f1024TowerLevel_functionFieldGenus_even,
    why24DecoderComplementDesignedDistance] at h
  simpa [f1024Why24OddDecodingRadius] using h
private theorem why24DecoderLocatorEquationFunctional_eq_zero (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ∈
      LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :
    why24DecoderLocatorEquationFunctional r syndrome locator = 0 := by
  rw [LinearMap.mem_ker] at hlocator
  apply (Module.finBasis F1024
    (GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r))).ext
  intro equation
  have hcoordinate := congrFun hlocator equation
  simp only [why24DecoderLocatorEquationFunctional,
    why24DecoderMultiplyLocatorIntoShortened,
    f1024Why24OddDecoderLinearSystem, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.zero_apply] at hcoordinate ⊢
  exact hcoordinate
private theorem why24DecoderLocatorProductWord_mem_complementDual (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ∈ LinearMap.ker
      (f1024Why24OddDecoderLinearSystem r
        (f1024Why24OddZSyndromeMap r error))) :
    why24DecoderLocatorProductWord r error locator ∈
      (why24DecoderComplementAGCode r).dual.carrier := by
  rw [LinearCode.mem_dual]
  intro word hword
  change word ∈ (agEvaluationLinearMap
    (f1024Why24OddDecoderComplementDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderComplementDivisor_apply_physical r)).range at hword
  rcases hword with ⟨row, rfl⟩
  have hfunctional := LinearMap.congr_fun
    (why24DecoderLocatorEquationFunctional_eq_zero r
      (f1024Why24OddZSyndromeMap r error) locator hlocator) row
  rw [LinearMap.zero_apply] at hfunctional
  change why24DecoderSyndromePairing r
      (f1024Why24OddZSyndromeMap r error)
      (why24DecoderScaledEvaluationToStabilizer r
        (why24DecoderMultiplyIntoShortened r row locator)) = 0 at hfunctional
  rw [why24DecoderSyndromePairing_mk, wordPairing_apply] at hfunctional
  rw [wordPairing_apply]
  calc
    ∑ site, why24DecoderLocatorProductWord r error locator site *
        agEvaluationLinearMap
          (f1024Why24OddDecoderComplementDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (why24DecoderComplementDivisor_apply_physical r) row site =
      ∑ site, error site *
        why24DecoderScaledEvaluationLinearMap r
          (why24DecoderMultiplyIntoShortened r row locator) site := by
            apply Finset.sum_congr rfl
            intro site _
            rw [why24DecoderScaledEvaluation_mul_apply]
            simp only [why24DecoderLocatorProductWord]
            ring
    _ = 0 := hfunctional
private theorem why24DecoderLocatorProductWord_hammingWeight_le (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    HammingWeight (why24DecoderLocatorProductWord r error locator) ≤
      HammingWeight error := by
  rw [HammingWeight_eq_card_hammingSupport,
    HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card
  intro site hsite
  have hproduct : why24DecoderLocatorProductWord r error locator site ≠ 0 :=
    (Finset.mem_filter.mp hsite).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ site, ?_⟩
  intro hzero
  apply hproduct
  change error site * _ = 0
  exact mul_eq_zero.mpr (Or.inl hzero)
private theorem why24DecoderLocatorProductWord_eq_zero (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r)
    (hlocator : locator ∈ LinearMap.ker
      (f1024Why24OddDecoderLinearSystem r
        (f1024Why24OddZSyndromeMap r error))) :
    why24DecoderLocatorProductWord r error locator = 0 := by
  classical
  by_contra hnonzero
  have hminimum :
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (why24DecoderComplementAGCode r).dual ≤
        (HammingWeight
          (why24DecoderLocatorProductWord r error locator) : WithTop Nat) := by
    rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
    exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
      ⟨why24DecoderLocatorProductWord_mem_complementDual r error locator
        hlocator, hnonzero⟩
  have hlower : f1024Why24OddDecodingRadius r + 2 ≤
      HammingWeight (why24DecoderLocatorProductWord r error locator) := by
    exact_mod_cast
      (why24DecoderComplementAGCode_dual_distance_lower_bound r |>.trans
        hminimum)
  have hupper : HammingWeight
      (why24DecoderLocatorProductWord r error locator) ≤
        f1024Why24OddDecodingRadius r :=
    (why24DecoderLocatorProductWord_hammingWeight_le r error locator).trans
      herror
  omega
private theorem why24DecoderLocatorZeroSet_card_le (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ≠ 0) :
    (why24DecoderLocatorZeroSet r locator).card ≤
      selectedAuxiliaryDegree (oddGenus r) := by
  let zeroSet := why24DecoderLocatorZeroSet r locator
  have hzeroOn : forall site, site ∈ zeroSet →
      agEvaluationLinearMap
        (f1024Why24OddDecoderAuxiliaryDivisor r)
        (f1024Why24OddPhysicalRationalPlace r)
        (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0 := by
    intro site hsite
    exact (Finset.mem_filter.mp hsite).2
  have hmem : (locator : F1024TowerLevel (2 * r + 2)) ∈
      GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r -
          zeroCoordinateDivisor
            (f1024Why24OddPhysicalRationalPlace r) zeroSet) :=
    evaluationZeroOn_mem_riemannRochSubmodule_sub
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (why24DecoderPhysicalRationalPlace_injective r)
      (f1024Why24OddDecoderAuxiliary_disjoint r)
      zeroSet locator hzeroOn
  have hnotNegative : ¬ Divisor.degree
      (GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
      (f1024Why24OddDecoderAuxiliaryDivisor r -
        zeroCoordinateDivisor
          (f1024Why24OddPhysicalRationalPlace r) zeroSet) < 0 := by
    intro hnegative
    have hbot := GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
      F1024 (F1024TowerLevel (2 * r + 2))
      (f1024Why24OddDecoderAuxiliaryDivisor r -
        zeroCoordinateDivisor
          (f1024Why24OddPhysicalRationalPlace r) zeroSet) hnegative
    have hfunctionZero :
        (locator : F1024TowerLevel (2 * r + 2)) = 0 := by
      have hmemBot : (locator : F1024TowerLevel (2 * r + 2)) ∈
          (⊥ : Submodule F1024 (F1024TowerLevel (2 * r + 2))) := by
        rw [← hbot]
        exact hmem
      exact (Submodule.mem_bot F1024).mp hmemBot
    apply hlocator
    apply Subtype.ext
    exact hfunctionZero
  rw [Divisor.degree_sub, f1024Why24OddDecoderAuxiliaryDivisor_degree,
    zeroCoordinateDivisor_degree_eq_card] at hnotNegative
  exact_mod_cast (show (zeroSet.card : Int) ≤
      selectedAuxiliaryDegree (oddGenus r) by omega)
private theorem why24DecoderRecoveryRangeSection_rightInverse (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (value : LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)) :
    why24DecoderRecoverySyndromeMap r syndrome
        (why24DecoderRecoveryRangeSection r syndrome value) = value.1 := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  let basis := Module.finBasis F1024 (LinearMap.range recovery)
  have hcoordinates := LinearMap.leftInverse_splittingOfFunOnFintypeSurjective
    (why24DecoderRecoveryCoordinates r syndrome)
    (why24DecoderRecoveryCoordinates_surjective r syndrome)
    (basis.equivFun value)
  have hrange : recovery.rangeRestrict
      (why24DecoderRecoveryRangeSection r syndrome value) = value := by
    apply basis.equivFun.injective
    exact hcoordinates
  exact congrArg Subtype.val hrange
private theorem why24DecoderError_mem_selectedRecoveryKernel (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    error ∈ LinearMap.ker
      (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r (f1024Why24OddZSyndromeMap r error))) := by
  rw [LinearMap.mem_ker]
  exact why24DecoderLocatorProductWord_eq_zero r error _ herror
    (why24DecoderLocator_mem_kernel r
      (f1024Why24OddZSyndromeMap r error))
private theorem why24DecoderRecoveryKernel_hammingWeight_le_zeroSet (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (word : Word F1024 (f1024Why24OddPhysicalSite r))
    (hword : word ∈ LinearMap.ker
      (why24DecoderLocatorProductLinearMap r locator)) :
    HammingWeight word ≤ (why24DecoderLocatorZeroSet r locator).card := by
  rw [HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card
  intro site hsite
  have hword_ne : word site ≠ 0 := by
    simpa [hammingSupport] using hsite
  have hproduct := congrFun (LinearMap.mem_ker.mp hword) site
  change word site *
      (f1024Why24OddCoordinateWeight r site.1 *
        agEvaluationLinearMap
          (f1024Why24OddDecoderAuxiliaryDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddDecoderAuxiliary_disjoint r) locator site) = 0 at hproduct
  have hevaluation : agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0 := by
    rcases mul_eq_zero.mp hproduct with hzero | hzero
    · exact False.elim (hword_ne hzero)
    · rcases mul_eq_zero.mp hzero with hzero | hzero
      · exact False.elim
          (f1024Why24OddCoordinateWeight_ne_zero r site.1 hzero)
      · exact hzero
  rw [why24DecoderLocatorZeroSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ site, ?_⟩
  change agEvaluationLinearMap
    (f1024Why24OddDecoderAuxiliaryDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0
  exact hevaluation
private theorem why24DecoderError_syndrome_mem_recoveryRange (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    f1024Why24OddZSyndromeMap r error ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r
        (f1024Why24OddZSyndromeMap r error)) := by
  let supported : LinearMap.ker
      (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r (f1024Why24OddZSyndromeMap r error))) :=
    ⟨error, why24DecoderError_mem_selectedRecoveryKernel r error herror⟩
  exact ⟨supported, rfl⟩
private theorem why24Decoder_syndrome_eq_of_mem_recoveryRange (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)) :
    f1024Why24OddZSyndromeMap r
        (f1024Why24OddAGDualDecoder r syndrome) = syndrome := by
  classical
  rw [f1024Why24OddAGDualDecoder, dif_pos hmem]
  exact why24DecoderRecoveryRangeSection_rightInverse r syndrome
    ⟨syndrome, hmem⟩
private theorem why24Decoder_mem_recoveryKernel_of_mem_range (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)) :
    f1024Why24OddAGDualDecoder r syndrome ∈
      LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) := by
  classical
  rw [f1024Why24OddAGDualDecoder, dif_pos hmem]
  exact (why24DecoderRecoveryRangeSection r syndrome
    ⟨syndrome, hmem⟩).2
private theorem why24DecoderSelectedAuxiliary_add_radius_lt_distance
    (r : Nat) :
    selectedAuxiliaryDegree (oddGenus r) +
        f1024Why24OddDecodingRadius r <
      selectedDistanceLowerBound (oddGenus r) := by
  have hmod := why24DecoderOddGenus_mod_eight r
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [f1024Why24OddDecodingRadius, selectedAuxiliaryDegree,
    selectedDecodingRadius, selectedDistanceLowerBound,
    selectedDivisorDegree, selectedLogicalCount]
  omega
private theorem why24DecoderHammingWeight_neg (r : Nat)
    (word : Word F1024 (f1024Why24OddPhysicalSite r)) :
    HammingWeight (-word) = HammingWeight word := by
  unfold HammingWeight hammingSupport
  congr 1
  ext site
  simp
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
theorem _root_.solution (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    f1024Why24OddAGDualDecoder r
      (f1024Why24OddZSyndromeMap r error) = error := by
  classical
  let syndrome := f1024Why24OddZSyndromeMap r error
  let decoded := f1024Why24OddAGDualDecoder r syndrome
  have hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome) :=
    why24DecoderError_syndrome_mem_recoveryRange r error herror
  have hdecodedKernel : decoded ∈
      LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) :=
    why24Decoder_mem_recoveryKernel_of_mem_range r syndrome hmem
  have hlocator_ne : why24DecoderLocator r syndrome ≠ 0 :=
    why24DecoderLocator_ne_zero_of_error r error herror
  have hdecodedWeight : HammingWeight decoded ≤
      selectedAuxiliaryDegree (oddGenus r) :=
    (why24DecoderRecoveryKernel_hammingWeight_le_zeroSet r
      (why24DecoderLocator r syndrome) decoded hdecodedKernel).trans
        (why24DecoderLocatorZeroSet_card_le r _ hlocator_ne)
  have hsyndrome : f1024Why24OddZSyndromeMap r decoded =
      f1024Why24OddZSyndromeMap r error :=
    why24Decoder_syndrome_eq_of_mem_recoveryRange r syndrome hmem
  by_contra hne
  have hdifference_mem : decoded - error ∈
      (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier := by
    change Submodule.Quotient.mk decoded = Submodule.Quotient.mk error at hsyndrome
    rwa [Submodule.Quotient.eq] at hsyndrome
  have hdifference_ne : decoded - error ≠ 0 := sub_ne_zero.mpr hne
  have hminimum :
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (f1024Why24OddWeightedMatrix r).stabilizerCode.dual ≤
        (HammingWeight (decoded - error) : WithTop Nat) := by
    rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
    exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
      ⟨hdifference_mem, hdifference_ne⟩
  have hlower : selectedDistanceLowerBound (oddGenus r) ≤
      HammingWeight (decoded - error) := by
    exact_mod_cast
      (f1024Why24OddStabilizerCode_dual_distance_lower_bound r |>.trans
        hminimum)
  have hupper : HammingWeight (decoded - error) ≤
      selectedAuxiliaryDegree (oddGenus r) +
        f1024Why24OddDecodingRadius r := by
    calc
      HammingWeight (decoded - error) =
          HammingWeight (decoded + -error) := by rw [sub_eq_add_neg]
      _ ≤ HammingWeight decoded + HammingWeight (-error) :=
        HammingWeight_add_le decoded (-error)
      _ = HammingWeight decoded + HammingWeight error := by
        rw [why24DecoderHammingWeight_neg]
      _ ≤ selectedAuxiliaryDegree (oddGenus r) +
          f1024Why24OddDecodingRadius r := Nat.add_le_add hdecodedWeight herror
  exact (not_lt_of_ge hlower)
    (hupper.trans_lt
      (why24DecoderSelectedAuxiliary_add_radius_lt_distance r))
end QEC.Distillation.Why24OneRoundProtocol
