-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.why24OneRoundFailureMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:56:27.076562+00:00
-- url     : https://prove2.me/submissions/6416ad11-c22a-43b0-aed6-e12fa33c85cf

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
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_Why24LocalStochasticPreparation_why24LocalStochastic_tail_maxRate
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
namespace Why24OneRoundTwirledConversionLaw
variable {r : Nat}
variable {preparation : Why24LocalStochasticPreparation
  (Fin (why24OneRoundInputCount r))
  (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
end Why24OneRoundTwirledConversionLaw
private theorem why24OneRoundFailureMass_le_failingFaultMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    why24OneRoundFailureMassForLaw r preparation law ≤
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        if why24OneRoundFaultFails r law fault then
          preparation.faultMass fault
        else 0 := by
  unfold why24OneRoundFailureMassForLaw
  apply Finset.sum_le_sum
  intro fault _
  by_cases hfails : why24OneRoundFaultFails r law fault
  · rw [if_pos hfails]
    calc
      (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
          if f1024Why24OddDecodingRadius r < HammingWeight error then
            law.branchMass fault error
          else 0) ≤
          ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
            law.branchMass fault error := by
              apply Finset.sum_le_sum
              intro error _
              by_cases herror :
                  f1024Why24OddDecodingRadius r < HammingWeight error
              · rw [if_pos herror]
              · rw [if_neg herror]
                exact law.branchMass_nonneg fault error
      _ = preparation.faultMass fault := law.branchMass_sum fault
  · rw [if_neg hfails]
    have hzero : ∀ error : Why24Word (f1024Why24OddPhysicalSite r),
        (if f1024Why24OddDecodingRadius r < HammingWeight error then
            law.branchMass fault error
          else 0) = 0 := by
      intro error
      by_cases herror :
          f1024Why24OddDecodingRadius r < HammingWeight error
      · rw [if_pos herror]
        by_contra hmass
        exact hfails ⟨error, herror, hmass⟩
      · rw [if_neg herror]
    simp_rw [hzero]
    simp
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
private theorem why24OneRound_exists_witness_of_faultFails (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (hfails : why24OneRoundFaultFails r law fault) :
    ∃ sites ∈ (Finset.univ :
        Finset (f1024Why24OddPhysicalSite r)).powersetCard
          (f1024Why24OddDecodingRadius r + 1),
      ∃ gate : {site // site ∈ sites} → Fin 70,
        why24OneRoundWitnessLocations r sites gate ⊆ fault := by
  rcases hfails with ⟨error, hweight, hmass⟩
  have hcard : f1024Why24OddDecodingRadius r + 1 ≤
      (hammingSupport error).card := by
    rw [← HammingWeight_eq_card_hammingSupport]
    omega
  obtain ⟨sites, hsites, hsitesCard⟩ :=
    Finset.exists_subset_card_eq hcard
  have hsitesPowerset : sites ∈
      (Finset.univ : Finset (f1024Why24OddPhysicalSite r)).powersetCard
        (f1024Why24OddDecodingRadius r + 1) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ sites, hsitesCard⟩
  have hgate : ∀ site : {site // site ∈ sites}, ∃ gate : Fin 70,
      why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site.1, gate) ∈ fault := by
    intro site
    apply law.error_supported fault error hmass site.1
    have hsupport : site.1 ∈ hammingSupport error := hsites site.2
    simpa [hammingSupport] using hsupport
  choose gate hgate using hgate
  refine ⟨sites, hsitesPowerset, gate, ?_⟩
  intro location hlocation
  rw [why24OneRoundWitnessLocations, Finset.mem_image] at hlocation
  rcases hlocation with ⟨site, _hsite, rfl⟩
  exact hgate site
private theorem why24OneRoundWitnessFaultMass_le (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) :
    why24OneRoundWitnessFaultMass r preparation sites gate ≤
      preparation.rate ^ sites.card := by
  exact preparation.why24LocalStochastic_tail_maxRate
    (why24OneRoundWitnessLocations r sites gate) |>.trans_eq (by simp)
private theorem why24OneRound_failingFaultMass_le_witnessSum (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    (∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        if why24OneRoundFaultFails r law fault then
          preparation.faultMass fault
        else 0) ≤
      ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard
              (f1024Why24OddDecodingRadius r + 1),
        ∑ gate : {site // site ∈ sites} → Fin 70,
          why24OneRoundWitnessFaultMass r preparation sites gate := by
  calc
    (∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        if why24OneRoundFaultFails r law fault then
          preparation.faultMass fault
        else 0) ≤
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ sites ∈
            (Finset.univ : Finset
              (f1024Why24OddPhysicalSite r)).powersetCard
                (f1024Why24OddDecodingRadius r + 1),
          ∑ gate : {site // site ∈ sites} → Fin 70,
            if why24OneRoundWitnessLocations r sites gate ⊆ fault then
              preparation.faultMass fault
            else 0 := by
      apply Finset.sum_le_sum
      intro fault _
      by_cases hfails : why24OneRoundFaultFails r law fault
      · rw [if_pos hfails]
        obtain ⟨sites, hsites, gate, hsubset⟩ :=
          why24OneRound_exists_witness_of_faultFails r preparation law fault hfails
        have hgateNonneg : ∀ candidate : {site // site ∈ sites} → Fin 70,
            0 ≤ if why24OneRoundWitnessLocations r sites candidate ⊆ fault then
              preparation.faultMass fault
            else 0 := by
          intro candidate
          split_ifs
          · exact preparation.faultMass_nonneg fault
          · exact le_rfl
        have hgateLe : preparation.faultMass fault ≤
            ∑ candidate : {site // site ∈ sites} → Fin 70,
              if why24OneRoundWitnessLocations r sites candidate ⊆ fault then
                preparation.faultMass fault
              else 0 := by
          calc
            preparation.faultMass fault =
                if why24OneRoundWitnessLocations r sites gate ⊆ fault then
                  preparation.faultMass fault
                else 0 := by rw [if_pos hsubset]
            _ ≤ _ := Finset.single_le_sum
              (fun candidate _ => hgateNonneg candidate) (Finset.mem_univ gate)
        have hsiteNonneg : ∀ candidate ∈
            (Finset.univ : Finset
              (f1024Why24OddPhysicalSite r)).powersetCard
                (f1024Why24OddDecodingRadius r + 1),
            0 ≤ ∑ candidateGate : {site // site ∈ candidate} → Fin 70,
              if why24OneRoundWitnessLocations r candidate candidateGate ⊆ fault then
                preparation.faultMass fault
              else 0 := by
          intro candidate _
          exact Finset.sum_nonneg fun candidateGate _ => by
            split_ifs
            · exact preparation.faultMass_nonneg fault
            · exact le_rfl
        have hsiteLe :
            (∑ candidate : {site // site ∈ sites} → Fin 70,
                if why24OneRoundWitnessLocations r sites candidate ⊆ fault then
                  preparation.faultMass fault
                else 0) ≤
              ∑ candidate ∈
                  (Finset.univ : Finset
                    (f1024Why24OddPhysicalSite r)).powersetCard
                      (f1024Why24OddDecodingRadius r + 1),
                ∑ candidateGate : {site // site ∈ candidate} → Fin 70,
                  if why24OneRoundWitnessLocations r candidate candidateGate ⊆ fault then
                    preparation.faultMass fault
                  else 0 :=
          Finset.single_le_sum hsiteNonneg hsites
        exact hgateLe.trans hsiteLe
      · rw [if_neg hfails]
        exact Finset.sum_nonneg fun sites _ =>
          Finset.sum_nonneg fun gate _ => by
            split_ifs
            · exact preparation.faultMass_nonneg fault
            · exact le_rfl
    _ = ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard
              (f1024Why24OddDecodingRadius r + 1),
        ∑ gate : {site // site ∈ sites} → Fin 70,
          why24OneRoundWitnessFaultMass r preparation sites gate := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sites _
      rw [Finset.sum_comm]
      rfl
private theorem why24OneRoundFailureMassForLaw_le (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    why24OneRoundFailureMassForLaw r preparation law ≤
      (Nat.choose (f1024Why24OddLength r)
        (f1024Why24OddDecodingRadius r + 1) : Real) *
        (70 * preparation.rate) ^
          (f1024Why24OddDecodingRadius r + 1) := by
  let k := f1024Why24OddDecodingRadius r + 1
  calc
    why24OneRoundFailureMassForLaw r preparation law ≤
        ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
          if why24OneRoundFaultFails r law fault then
            preparation.faultMass fault
          else 0 :=
      why24OneRoundFailureMass_le_failingFaultMass r preparation law
    _ ≤ ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard k,
        ∑ gate : {site // site ∈ sites} → Fin 70,
          why24OneRoundWitnessFaultMass r preparation sites gate :=
      why24OneRound_failingFaultMass_le_witnessSum r preparation law
    _ ≤ ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard k,
        ∑ _gate : {site // site ∈ sites} → Fin 70,
          preparation.rate ^ k := by
      apply Finset.sum_le_sum
      intro sites hsites
      apply Finset.sum_le_sum
      intro gate _
      have hcard := (Finset.mem_powersetCard.mp hsites).2
      simpa [k, hcard] using
        why24OneRoundWitnessFaultMass_le r preparation sites gate
    _ = (Nat.choose (f1024Why24OddLength r) k : Real) *
          (70 * preparation.rate) ^ k := by
      have hinner : ∀ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard k,
          (∑ _gate : {site // site ∈ sites} → Fin 70,
              preparation.rate ^ k) =
            (70 : Real) ^ k * preparation.rate ^ k := by
        intro sites hsites
        have hcard := (Finset.mem_powersetCard.mp hsites).2
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [Fintype.card_fin, hcard]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul,
        Finset.card_powersetCard, Finset.card_univ,
        show Fintype.card (f1024Why24OddPhysicalSite r) =
            f1024Why24OddLength r by rfl]
      ring
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
    why24OneRoundFailureMass r preparation ≤
      (Nat.choose (f1024Why24OddLength r)
        (f1024Why24OddDecodingRadius r + 1) : Real) *
        (70 * preparation.rate) ^
          (f1024Why24OddDecodingRadius r + 1) := by
  simpa [why24OneRoundFailureMass] using
    why24OneRoundFailureMassForLaw_le r preparation
      (why24OneRoundDerivedTwirledConversionLaw r preparation)
end QEC.Distillation.Why24OneRoundProtocol
