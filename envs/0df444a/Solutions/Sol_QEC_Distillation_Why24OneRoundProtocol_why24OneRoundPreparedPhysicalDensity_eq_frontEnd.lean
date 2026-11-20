-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.why24OneRoundPreparedPhysicalDensity_eq_frontEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:48:17.128851+00:00
-- url     : https://prove2.me/submissions/ff6a6d29-6d9d-4036-bbb0-7d885c408415

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
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
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
private theorem why24Inner_apply_real_of_positive
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    (rho : DensityOperator H) (u : H) :
    ((inner Complex u (rho.toOperator u)).re : Complex) =
      inner Complex u (rho.toOperator u) := by
  have hpositive := (LinearMap.isPositive_iff_complex rho.toOperator).mp
    rho.positive u
  simpa [rho.positive.isSymmetric u u] using hpositive.1
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
private theorem why24MeasurePrepare_sandwich
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (output : K) (input : H) (A : Operator H) :
    (InnerProductSpace.rankOne Complex output input).toLinearMap.comp
        (A.comp (LinearMap.adjoint
          (InnerProductSpace.rankOne Complex output input).toLinearMap)) =
      (inner Complex input (A input)) •
        (InnerProductSpace.rankOne Complex output output).toLinearMap := by
  have hadjoint :
      LinearMap.adjoint
          (InnerProductSpace.rankOne Complex output input).toLinearMap =
        (InnerProductSpace.rankOne Complex input output).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex output input).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  rw [hadjoint]
  ext vector
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    smul_smul, mul_comm]
private theorem why24OneRoundFrontEnd_branchDensity_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    ((why24OneRoundFrontEndChannel r).mapDensity
      (preparation.branchDensity fault)).toOperator =
      ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
        (why24OneRoundJointBornWeight r preparation fault error : Complex) •
          (why24OneRoundErrorDensity r
            (why24OneRoundAppendixErrorWord r error)).toOperator := by
  rw [QuantumChannel.mapDensity_toOperator,
    why24OneRoundFrontEndChannel,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro error _
  simp only [why24OneRoundFrontEndKraus]
  rw [why24MeasurePrepare_sandwich]
  rw [← why24Inner_apply_real_of_positive
    (preparation.branchDensity fault)
    (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)]
  rfl
namespace Why24OneRoundTwirledConversionLaw
variable {r : Nat}
variable {preparation : Why24LocalStochasticPreparation
  (Fin (why24OneRoundInputCount r))
  (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
end Why24OneRoundTwirledConversionLaw
private theorem why24OneRoundDerivedMixture_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundPreparedPhysicalDensityForLaw r preparation
      (why24OneRoundDerivedTwirledConversionLaw r preparation)).toOperator =
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
          ((preparation.faultMass fault *
              why24OneRoundJointBornWeight r preparation fault error : Real) :
            Complex) •
            (why24OneRoundErrorDensity r
              (why24OneRoundAppendixErrorWord r error)).toOperator := by
  rw [why24OneRoundPreparedPhysicalDensityForLaw,
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  simp only [Why24OneRoundTwirledConversionLaw.errorMass,
    why24OneRoundDerivedTwirledConversionLaw,
    why24OneRoundDerivedBranchMass]
  calc
    (∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
        ((∑ fault : Finset (Fin (why24OneRoundInputCount r)),
          ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
            if fieldError = why24OneRoundAppendixErrorWord r error then
              preparation.faultMass fault *
                why24OneRoundJointBornWeight r preparation fault error
            else 0 : Real) : Complex) •
          (why24OneRoundErrorDensity r fieldError).toOperator) =
      ∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
        ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
          ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
            ((if fieldError = why24OneRoundAppendixErrorWord r error then
                preparation.faultMass fault *
                  why24OneRoundJointBornWeight r preparation fault error
              else 0 : Real) : Complex) •
              (why24OneRoundErrorDensity r fieldError).toOperator := by
        apply Finset.sum_congr rfl
        intro fieldError _
        rw [Complex.ofReal_sum, Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro fault _
        rw [Complex.ofReal_sum, Finset.sum_smul]
    _ = ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
          ∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
            ((if fieldError = why24OneRoundAppendixErrorWord r error then
                preparation.faultMass fault *
                  why24OneRoundJointBornWeight r preparation fault error
              else 0 : Real) : Complex) •
              (why24OneRoundErrorDensity r fieldError).toOperator := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro fault _
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro fault _
      apply Finset.sum_congr rfl
      intro error _
      rw [Finset.sum_eq_single (why24OneRoundAppendixErrorWord r error)]
      · rw [if_pos rfl]
      · intro fieldError _ hne
        rw [if_neg hne]
        simp
      · simp
private theorem why24OneRoundFrontEnd_prepared_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    ((why24OneRoundFrontEndChannel r).mapDensity
      preparation.why24LocalStochasticPreparedDensity).toOperator =
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
          ((preparation.faultMass fault *
              why24OneRoundJointBornWeight r preparation fault error : Real) :
            Complex) •
            (why24OneRoundErrorDensity r
              (why24OneRoundAppendixErrorWord r error)).toOperator := by
  rw [QuantumChannel.mapDensity_toOperator,
    preparation.why24LocalStochasticPreparedDensity_toOperator, map_sum]
  apply Finset.sum_congr rfl
  intro fault _
  rw [map_smul, ← QuantumChannel.mapDensity_toOperator,
    why24OneRoundFrontEnd_branchDensity_toOperator, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro error _
  rw [smul_smul, ← Complex.ofReal_mul]
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
    why24OneRoundPreparedPhysicalDensity r preparation =
      (why24OneRoundFrontEndChannel r).mapDensity
        preparation.why24LocalStochasticPreparedDensity := by
  apply DensityOperator.ext_toOperator
  rw [why24OneRoundPreparedPhysicalDensity,
    why24OneRoundDerivedMixture_toOperator,
    why24OneRoundFrontEnd_prepared_toOperator]
end QEC.Distillation.Why24OneRoundProtocol
