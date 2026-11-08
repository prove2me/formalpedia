-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_pk22LPSFamily_of_fourSqrtBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:35:46.06089+00:00
-- url     : https://prove2.me/submissions/470a07f4-9085-45ee-9bf5-cb197c6e0512

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCodeFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGoodFamilyAssembly
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_A
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_B
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_dualData
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inl_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inr_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_neg
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedUnswapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedUnswapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_CompatibleDegreePrime_blocks_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_CompatibleDegreePrime_degree_eq_block_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyRightRegularRepresentation_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyVectorWordProduct_lps_backtrack
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coe_lpsQuaternionAwayWordProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22CompatibleLocalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsBacktrackingPrefixEquiv_symm_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFinRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPGLHeckeLabel_eq_toPGL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrefixTerm_backtrackingPrefixEquiv_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrefixTerm_reducedPrefixEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_append
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_cons
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_nil
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_singleton
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordConsEquiv_symm_tail
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_neg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSemanticFamily_hasEventualRateAtLeast_of_local_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsVertexGroup_card_cofinal
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_lpsQuaternionWordProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_scale_bounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_lpsFinQuaternionFamilyLabel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticFamily_isAsymptoticallyGood_of_partiteMixingBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyConstantProjection
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
attribute [local simp] QEC.Coding.LiftedProduct.dualData_A
attribute [local simp] QEC.Coding.LiftedProduct.dualData_B
attribute [local simp] QEC.Coding.LiftedProduct.dualData_dualData
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inl_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inr_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_neg
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedSwapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedUnswapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedUnswapWord_signedSwapWord
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyRightRegularRepresentation_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lps_backtrack
attribute [local simp] QEC.Coding.TannerLiftedProduct.coe_lpsQuaternionAwayWordProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsBacktrackingPrefixEquiv_symm_product
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPGLHeckeLabel_eq_toPGL
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPrefixTerm_backtrackingPrefixEquiv_symm
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPrefixTerm_reducedPrefixEquiv
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_conj
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_append
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_cons
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_singleton
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordConsEquiv_symm_tail
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_neg
attribute [local simp] QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionWordProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.trace_cayleyConstantProjection
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


section
namespace QEC.Coding.TannerLiftedProduct
private theorem log_two_mul_block_bound
    (A N x : ℕ) (hA : 0 < A) (hNPositive : 0 < N) (hx : 0 < x)
    (hN : N ≤ 64 * x ^ 6) :
    Nat.log 2 (2 * (A * N)) + 1 ≤ 128 * A + 6 * x + 1 := by
  have hAexp : A < 2 ^ A := A.lt_two_pow_self
  have hxexp : x < 2 ^ x := x.lt_two_pow_self
  have hxpow : x ^ 6 ≤ (2 ^ x) ^ 6 :=
    Nat.pow_le_pow_left hxexp.le 6
  have harg : 2 * (A * N) < 2 ^ (128 * A + 6 * x + 1) := by
    calc
      2 * (A * N) ≤ 2 * (A * (64 * x ^ 6)) := by gcongr
      _ = 128 * A * x ^ 6 := by ring
      _ < 128 * 2 ^ A * x ^ 6 := by gcongr
      _ ≤ 128 * 2 ^ A * (2 ^ x) ^ 6 := by gcongr
      _ = 2 ^ 7 * 2 ^ A * 2 ^ (6 * x) := by
        simp [pow_mul, Nat.mul_comm]
      _ = 2 ^ (7 + A + 6 * x) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (128 * A + 6 * x + 1) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
  have hlog : Nat.log 2 (2 * (A * N)) < 128 * A + 6 * x + 1 :=
    Nat.log_lt_of_lt_pow (by positivity) harg
  omega
private theorem le_twelve_mul_nthRoot_six_pow
    (N x : ℕ) (hx : x = Nat.nthRoot 6 N)
    (hxTwo : 2 ≤ x) :
    N ≤ 12 * x ^ 6 := by
  have hUpper : N < (x + 1) ^ 6 := by
    subst x
    exact Nat.lt_pow_nthRoot_add_one (by norm_num) N
  have hLinear : 2 * (x + 1) ≤ 3 * x := by omega
  have hPow := Nat.pow_le_pow_left hLinear 6
  have hScaled : 64 * (x + 1) ^ 6 ≤ 729 * x ^ 6 := by
    convert hPow using 1 <;> ring
  have hCrude : 64 * N < 768 * x ^ 6 := by
    calc
      64 * N < 64 * (x + 1) ^ 6 :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 64)).2 hUpper
      _ ≤ 729 * x ^ 6 := hScaled
      _ ≤ 768 * x ^ 6 := by
        apply Nat.mul_le_mul_right
        norm_num
  omega
private theorem four_sqrt_scale_add_one_le_schedule
    (q t x : ℕ)
    (a : CompatibleDegreePrime (pk22LocalWidth q t))
    (hx : 0 < x) (hUpper : a.blocks ≤ 12 * x ^ 6) :
    4 * Real.sqrt (a.p : ℝ) + 1 ≤
      ((pk22SpectralCoefficient q t * x ^ 3 : Nat) : ℝ) := by
  let U := pk22ParameterBase q t
  let X : ℕ := U ^ 2 * x ^ 3
  have hU : 0 < U := by simpa [U] using pk22ParameterBase_pos q t
  have hX : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by
      dsimp [X]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos hU) (Nat.pow_pos hx))))
  have hpDegree : a.p ≤ pk22LocalWidth q t * a.blocks := by
    rw [← a.degree_eq_block_mul]
    omega
  have hpBound : a.p ≤ 12 * X ^ 2 := by
    calc
      a.p ≤ pk22LocalWidth q t * a.blocks := hpDegree
      _ ≤ pk22LocalWidth q t * (12 * x ^ 6) := by gcongr
      _ = 12 * X ^ 2 := by
        unfold pk22LocalWidth
        dsimp [U, X]
        ring
  have hpReal : (a.p : ℝ) ≤ 12 * (X : ℝ) ^ 2 := by
    exact_mod_cast hpBound
  have hRoot : Real.sqrt (a.p : ℝ) ≤ (7 / 2 : ℝ) * X := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hCompare : 12 * (X : ℝ) ^ 2 ≤ ((7 / 2 : ℝ) * X) ^ 2 := by
        nlinarith [sq_nonneg (X : ℝ)]
      exact hpReal.trans hCompare
  calc
    4 * Real.sqrt (a.p : ℝ) + 1 ≤
        4 * ((7 / 2 : ℝ) * X) + 1 := by gcongr
    _ ≤ 16 * (X : ℝ) := by nlinarith
    _ = ((pk22SpectralCoefficient q t * x ^ 3 : Nat) : ℝ) := by
      unfold pk22SpectralCoefficient
      dsimp [U, X]
      push_cast
      ring
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LPSFamilyQubitDecidableEq
set_option maxHeartbeats 1200000
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : Type) [Field F] [Fintype F]
    (targetRate : ℝ) (hRatePositive : 0 < targetRate)
    (hRate : targetRate < 1)
    (hSpectral : ∀ (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ),
      SmallSetExpansion.HasMeanZeroBilinearBound
        (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
        (4 * Real.sqrt (p : ℝ))) :
    ∃ (t : ℕ)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      let hCount := card_lpsQuaternionShell_eq_prime_add_one
        a.prime a.oneModFour
      QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') ∧
        QEC.QLDPC.HasEventualRateAtLeast
          (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
  let _ : DecidableEq F := Classical.decEq F
  obtain ⟨t, a, h, h', hScale, hLength, hRank, h'Rank,
      hDistance, hDistanceReverse, hProductExpand,
      hProductExpandReverse, hRatio, _hSpectralScale⟩ :=
    exists_pk22CompatibleLocalPair F targetRate hRate
  let q := Nat.card F
  let N := a.blocks
  let x := Nat.nthRoot 6 N
  let D := pk22DistanceCoefficient q t
  let C := pk22SpectralCoefficient q t
  let S := pk22FaceCoefficient q t
  let w := a.p + 1
  let d := D * N
  let m := x ^ 4
  let s := S * x ^ 7
  let spectral : ℝ := 4 * Real.sqrt (a.p : ℝ)
  have hAPositive : 0 < pk22LocalWidth q t := by
    unfold pk22LocalWidth
    exact Nat.pow_pos (pk22ParameterBase_pos q t)
  have hNPositive : 0 < N := by
    exact a.blocks_pos hAPositive
  have hScale' : pk22ScaleThreshold q t ≤ x := by
    simpa [q, N, x] using hScale
  obtain ⟨hxPositive, hSmall, hBudgetCoefficient, hRectangleCoefficient,
      hVerticalCoefficient, hEdgeCoefficient, hFaceCoefficient,
      _hRectangleThreshold⟩ := pk22_scale_bounds q t x hScale'
  have hxLower : x ^ 6 ≤ N := by
    dsimp [x]
    exact Nat.pow_nthRoot_le (by norm_num)
  have hxEighteen : 18 ≤ x := by
    apply le_trans _ hScale'
    simp only [pk22ScaleThreshold]
    omega
  have hxUpper : N ≤ 12 * x ^ 6 :=
    le_twelve_mul_nthRoot_six_pow N x rfl (by omega)
  have hLog : Nat.log 2 (2 * w) + 1 ≤
      128 * pk22LocalWidth q t + 6 * x + 1 := by
    rw [show w = pk22LocalWidth q t * N by
      simpa [q, w, N] using a.degree_eq_block_mul]
    exact log_two_mul_block_bound _ _ _ hAPositive hNPositive
      hxPositive (hxUpper.trans (by gcongr; norm_num))
  have hLambdaSchedule : spectral + 1 ≤ ((C * x ^ 3 : Nat) : ℝ) := by
    simpa [spectral, C] using
      four_sqrt_scale_add_one_le_schedule q t x a hxPositive hxUpper
  have hFour : 4 ≤ d := by
    have hxTwoSix : x ^ 2 ≤ x ^ 6 :=
      Nat.pow_le_pow_right hxPositive (by norm_num)
    calc
      4 ≤ 12 := by omega
      _ ≤ D * x ^ 2 := by simpa [D] using hSmall
      _ ≤ D * x ^ 6 := Nat.mul_le_mul_left D hxTwoSix
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hDistanceScale : 4 * m ≤ d := by
    calc
      4 * x ^ 4 ≤ 12 * x ^ 4 :=
        Nat.mul_le_mul_right (x ^ 4) (by norm_num)
      _ ≤ (D * x ^ 2) * x ^ 4 := by
        exact Nat.mul_le_mul_right (x ^ 4) (by simpa [D] using hSmall)
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hRectangleScale : 4 * s ≤ m * d := by
    calc
      4 * (S * x ^ 7) = (4 * S) * x ^ 7 := by ring
      _ ≤ (D * x ^ 3) * x ^ 7 := by
        exact Nat.mul_le_mul_right (x ^ 7)
          (by simpa [D, S] using hRectangleCoefficient)
      _ = x ^ 4 * (D * x ^ 6) := by ring
      _ ≤ x ^ 4 * (D * N) := by gcongr
  have hBudgetNat : 12 * m + 6 ≤ d := by
    have hxFourPositive : 0 < x ^ 4 := Nat.pow_pos hxPositive
    calc
      12 * x ^ 4 + 6 ≤ 18 * x ^ 4 := by omega
      _ ≤ (D * x ^ 2) * x ^ 4 := by
        exact Nat.mul_le_mul_right (x ^ 4)
          (by simpa [D] using hBudgetCoefficient)
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hwPositive : (0 : ℝ) < w := by
    exact_mod_cast (show 0 < w by dsimp [w]; omega)
  have hBudget : 4 * (m : ℝ) + 2 ≤
      ((d : ℝ) / (3 * (w : ℝ))) * w := by
    have hBudgetReal : 12 * (m : ℝ) + 6 ≤ (d : ℝ) := by
      exact_mod_cast hBudgetNat
    have hCancel : ((d : ℝ) / (3 * (w : ℝ))) * w = (d : ℝ) / 3 := by
      field_simp
    rw [hCancel]
    linarith
  have hVerticalSchedule : 2 * m + C * x ^ 3 ≤ d := by
    have hxThreeFour : x ^ 3 ≤ x ^ 4 :=
      Nat.pow_le_pow_right hxPositive (by norm_num)
    calc
      2 * x ^ 4 + C * x ^ 3 ≤ 2 * x ^ 4 + C * x ^ 4 := by gcongr
      _ = (2 + C) * x ^ 4 := by ring
      _ ≤ (D * x ^ 2) * x ^ 4 := by
        exact Nat.mul_le_mul_right (x ^ 4)
          (by simpa [D, C] using hVerticalCoefficient)
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hxLower
  have hVertical : (2 * m : ℝ) + (spectral + 1) ≤ d := by
    have hScheduleReal : ((2 * m + C * x ^ 3 : Nat) : ℝ) ≤ d := by
      exact_mod_cast hVerticalSchedule
    push_cast at hScheduleReal
    push_cast at hLambdaSchedule
    nlinarith
  have hEdgeSchedule : 4 * (C * x ^ 3) ≤ m := by
    calc
      4 * (C * x ^ 3) = (4 * C) * x ^ 3 := by ring
      _ ≤ x * x ^ 3 := by
        exact Nat.mul_le_mul_right (x ^ 3)
          (by simpa [C] using hEdgeCoefficient)
      _ = x ^ 4 := by ring
  have hEdge : 2 * (2 * (spectral + 1)) ≤ (m : ℝ) := by
    have hScheduleReal : (4 * ((C * x ^ 3 : Nat) : ℝ)) ≤ (m : ℝ) := by
      exact_mod_cast hEdgeSchedule
    nlinarith
  have hFaceSchedule :
      16 * (Nat.log 2 (2 * w) + 1) * (C * x ^ 3) ^ 2 ≤ s := by
    calc
      16 * (Nat.log 2 (2 * w) + 1) * (C * x ^ 3) ^ 2 =
          (16 * (Nat.log 2 (2 * w) + 1) * C ^ 2) * x ^ 6 := by ring
      _ ≤ (16 * (128 * pk22LocalWidth q t + 6 * x + 1) * C ^ 2) *
          x ^ 6 := by gcongr
      _ ≤ (S * x) * x ^ 6 := by
        exact Nat.mul_le_mul_right (x ^ 6)
          (by simpa [C, S] using hFaceCoefficient)
      _ = S * x ^ 7 := by ring
  have hFace :
      2 * (((Nat.log 2 (2 * w) + 1 : Nat) : ℝ) *
        (8 * (spectral + 1) ^ 2)) ≤ (s : ℝ) := by
    have hScheduleReal :
        (16 * (Nat.log 2 (2 * w) + 1) * (C * x ^ 3) ^ 2 : ℕ) ≤ s :=
      hFaceSchedule
    have hScheduleReal' :
        (16 : ℝ) * (Nat.log 2 (2 * w) + 1) *
          (((C * x ^ 3 : Nat) : ℝ) ^ 2) ≤ (s : ℝ) := by
      exact_mod_cast hScheduleReal
    push_cast at hScheduleReal'
    have hLambdaNonnegative : 0 ≤ spectral + 1 := by
      dsimp [spectral]
      positivity
    have hSquare : (spectral + 1) ^ 2 ≤
        (((C * x ^ 3 : Nat) : ℝ) ^ 2) := by
      nlinarith [sq_nonneg
        (((C * x ^ 3 : Nat) : ℝ) - (spectral + 1))]
    push_cast at hSquare
    have hScaledSquare := mul_le_mul_of_nonneg_left hSquare
      (show (0 : ℝ) ≤ 16 * (Nat.log 2 (2 * w) + 1) by positivity)
    calc
      2 * (((Nat.log 2 (2 * w) + 1 : Nat) : ℝ) *
          (8 * (spectral + 1) ^ 2)) =
          16 * ((Nat.log 2 (2 * w) : ℝ) + 1) *
            (spectral + 1) ^ 2 := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ 16 * ((Nat.log 2 (2 * w) : ℝ) + 1) *
          ((C : ℝ) * x ^ 3) ^ 2 := hScaledSquare
      _ ≤ (s : ℝ) := hScheduleReal'
  let hCount := card_lpsQuaternionShell_eq_prime_add_one
    a.prime a.oneModFour
  let label := lpsFinQuaternionFamilyLabel
    a.prime a.oneModFour hCount
  have hMixing : ∀ n,
      HasPartiteExpanderMixingBound
        (rightDoubleCoverGraph (label n)) (Fintype.card (Fin w)) spectral := by
    intro n
    have hBase : SmallSetExpansion.HasMeanZeroBilinearBound
        (rightCayleyGraph (label n)) spectral := by
      rw [rightCayleyGraph_lpsFinQuaternionFamilyLabel]
      exact hSpectral a.p a.prime a.oneModFour n
    simpa [label, spectral, w] using
      lpsFinRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
        a.prime a.oneModFour hCount n spectral (by positivity) hBase
  have hGood : QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
      (lpsSemanticFamily a.prime a.oneModFour hCount h h') := by
    have hProductExpand' : ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h') s (2 * m)
        ((d : ℝ) / (3 * (w : ℝ))) := by
      simpa [q, N, x, D, S, d, m, s, w] using hProductExpand
    have hProductExpandReverse' : ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h) s (2 * m)
        ((d : ℝ) / (3 * (w : ℝ))) := by
      simpa [q, N, x, D, S, d, m, s, w] using hProductExpandReverse
    have hDistance' : ∀ c : Word F (Fin w),
        c ∈ (ProductExpansion.parityCheckCode h).carrier → c ≠ 0 →
        d ≤ HammingWeight c := by
      simpa [q, N, D, d, w] using hDistance
    have hDistanceReverse' : ∀ c : Word F (Fin w),
        c ∈ (ProductExpansion.parityCheckCode h').carrier → c ≠ 0 →
        d ≤ HammingWeight c := by
      simpa [q, N, D, d, w] using hDistanceReverse
    apply semanticFamily_isAsymptoticallyGood_of_partiteMixingBound
      label h h' (by simp) (lpsVertexGroup_card_cofinal a.prime a.oneModFour)
      hRank h'Rank
      d m s ((d : ℝ) / (3 * (w : ℝ)))
      hProductExpand' hProductExpandReverse' hDistance' hDistanceReverse'
      (by simpa [q, D, N, d] using hLength)
      (by
        have hpTwo := a.prime.two_le
        simp only [Fintype.card_fin]
        omega)
      hFour hDistanceScale hRectangleScale
      (by simpa [w] using hBudget)
      spectral (by dsimp [spectral]; positivity) hMixing hVertical hEdge
      (by simpa [w] using hFace)
      targetRate hRatePositive
    simpa [q, w] using hRatio
  have hRequestedRate : QEC.QLDPC.HasEventualRateAtLeast
      (lpsSemanticFamily a.prime a.oneModFour hCount h h') targetRate := by
    apply lpsSemanticFamily_hasEventualRateAtLeast_of_local_ratio
    simpa [q, w] using hRatio
  exact ⟨t, a, h, h', hGood, hRequestedRate⟩
end QEC.Coding.TannerLiftedProduct
