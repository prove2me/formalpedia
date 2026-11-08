-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPrimeQuaternionKernelPoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:02:27.556612+00:00
-- url     : https://prove2.me/submissions/7ace7348-934d-47db-ae92-800dfef99d6c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_matrix_mul_adjugate_eq_zero_of_ker_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasLPSParity_of_mem_lpsQuaternionShell_prime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasLPSParity_lpsQuaternionDiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_HasLPSParity_mul
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionDiv_mul_conj_mul_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionMatrix_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_cons
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_nil
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordConsEquiv_symm_tail
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_lpsQuaternionDiv_mul_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_lpsQuaternionWordProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyConstantProjection
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_cons
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordConsEquiv_symm_tail
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionWordProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.trace_cayleyConstantProjection
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) :
    Function.Injective (lpsPrimeQuaternionKernelPoint hp hp4) := by
  intro beta gamma hpoint
  have hbetaNorm : beta.1.norm = (p : ℤ) :=
    norm_eq_of_mem_lpsQuaternionShell hp.pos beta.2
  have hgammaNorm : gamma.1.norm = (p : ℤ) :=
    norm_eq_of_mem_lpsQuaternionShell hp.pos gamma.2
  have hbetaPrimitive : ¬beta.1.CoordinatesDvd (p : ℤ) :=
    not_coordinatesDvd_of_norm_eq_prime hp beta.1 hbetaNorm
  have hgammaPrimitive : ¬gamma.1.CoordinatesDvd (p : ℤ) :=
    not_coordinatesDvd_of_norm_eq_prime hp gamma.1 hgammaNorm
  have hpDvdBetaNorm : (p : ℤ) ∣ beta.1.norm :=
    ⟨1, by simpa [hbetaNorm]⟩
  have hpDvdGammaNorm : (p : ℤ) ∣ gamma.1.norm :=
    ⟨1, by simpa [hgammaNorm]⟩
  have hker :
      LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p beta.1)) =
        LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p gamma.1)) := by
    have hsub := congrArg Projectivization.submodule hpoint
    simpa [lpsPrimeQuaternionKernelPoint,
      lpsQuaternionKernelPoint_submodule hp hp4 beta.1
        hpDvdBetaNorm hbetaPrimitive,
      lpsQuaternionKernelPoint_submodule hp hp4 gamma.1
        hpDvdGammaNorm hgammaPrimitive] using hsub
  have hgammaDet : (lpsQuaternionMatrix p gamma.1).det = 0 := by
    rw [det_lpsQuaternionMatrix, hgammaNorm]
    simp
  have hmatrixProd :
      lpsQuaternionMatrix p beta.1 *
        (lpsQuaternionMatrix p gamma.1).adjugate = 0 :=
    matrix_mul_adjugate_eq_zero_of_ker_eq _ _ hgammaDet hker
  have hquatMatrix : lpsQuaternionMatrix p (beta.1 * gamma.1.conj) = 0 := by
    rw [lpsQuaternionMatrix_mul, lpsQuaternionMatrix_conj]
    exact hmatrixProd
  have hdiv : (beta.1 * gamma.1.conj).CoordinatesDvd (p : ℤ) :=
    (lpsQuaternionMatrix_eq_zero_iff_coordinatesDvd hp hp4 _).mp hquatMatrix
  let u := lpsQuaternionDiv (p : ℤ) (beta.1 * gamma.1.conj)
  have hfactor : u * gamma.1 = beta.1 :=
    lpsQuaternionDiv_mul_conj_mul_eq hp hgammaNorm hdiv
  have huNorm : u.norm = 1 := by
    simpa [u] using norm_lpsQuaternionDiv_mul_conj
      (n := 0) hp (by simpa using hbetaNorm) hgammaNorm hdiv
  have hpOddNat : Odd p := by
    have hdecomp := Nat.mod_add_div p 4
    refine ⟨2 * (p / 4), ?_⟩
    omega
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  have hbetaParity :=
    hasLPSParity_of_mem_lpsQuaternionShell_prime hp4 beta.2
  have hgammaParity :=
    hasLPSParity_of_mem_lpsQuaternionShell_prime hp4 gamma.2
  have huParity : u.HasLPSParity := by
    apply hasLPSParity_lpsQuaternionDiv hpOdd hdiv
    exact hbetaParity.mul hgammaParity.conj
  rcases eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity u huNorm huParity with
      hu | hu
  · apply Subtype.ext
    simpa [hu] using hfactor.symm
  · have hbetaPos :=
      ((mem_lpsQuaternionShell_iff hp.pos beta.1).mp beta.2).2.1
    have hgammaPos :=
      ((mem_lpsQuaternionShell_iff hp.pos gamma.1).mp gamma.2).2.1
    have ha := congrArg LPSQuaternion.a hfactor
    rw [hu] at ha
    simp at ha
    omega
end QEC.Coding.TannerLiftedProduct
