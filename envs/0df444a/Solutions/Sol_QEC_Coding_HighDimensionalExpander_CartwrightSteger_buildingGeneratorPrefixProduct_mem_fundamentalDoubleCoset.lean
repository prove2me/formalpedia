-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorPrefixProduct_mem_fundamentalDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:51:43.995695+00:00
-- url     : https://prove2.me/submissions/42bd01fb-5360-434a-9ee1-2e5a1e05bd5b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusYInv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicElement_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraSplitNormOneGeneratorRatio_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToGlobalSkewScalarRange_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalGL_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewExponentResidue_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentCyclicLaurentCoordinate_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToBuildingMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToCyclicAlgebra_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_map_mem_schreierCliqueComplex_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyOne
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyThree
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankFourBuildingAdjacencyTwo
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankThreeBuildingAdjacencyOne
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_adjoint_rankThreeBuildingAdjacencyTwo
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_one_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankThree_one_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalNeighborAdjacentEquiv_apply_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
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
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_RatFunc_coefficientRingEquiv_C
import Theorems.Thm_RatFunc_coefficientRingEquiv_X
import Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_arithmeticOnePlusY
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticRingToFunctionField_arithmeticOnePlusYInv
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLocalCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicElement_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingGL
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_constantCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicMonomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldCyclicBasis_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_generator
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_generator
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponentResidue_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_add
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentCyclicLaurentCoordinate_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToBuildingMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToCyclicAlgebra_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CayleyClique.map_mem_schreierCliqueComplex_iff
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyOne
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyThree
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankFourBuildingAdjacencyTwo
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankThreeBuildingAdjacencyOne
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_rankThreeBuildingAdjacencyTwo
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalNeighborAdjacentEquiv_apply_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourBuildingAdjacencyFamily_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyFamily_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeBuildingAdjacencyFamily_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply
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
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] RatFunc.coefficientRingEquiv_C
attribute [local simp] RatFunc.coefficientRingEquiv_X
attribute [local simp] RatFunc.coefficientRingEquiv_apply_div


section
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
private theorem list_ofFn_rankThree_local
    {A : Type*} (u : Fin 3 → A) :
    List.ofFn u = [u 0, u 1, u 2] := by
  apply List.ext_get
  · simp
  · intro n hna hnb
    change n < 3 at hna
    interval_cases n <;> simp
private theorem list_ofFn_rankFour_local
    {A : Type*} (u : Fin 4 → A) :
    List.ofFn u = [u 0, u 1, u 2, u 3] := by
  apply List.ext_get
  · simp
  · intro n hna hnb
    change n < 4 at hna
    interval_cases n <;> simp
private theorem buildingGeneratorWordProduct_rankThree_local
    (P : BasePrime) (u : Fin 3 → ConstantProjectiveClass P .three) :
    buildingGeneratorWordProduct P .three (List.ofFn u) =
      (buildingLatticeGenerator P .three (u 0) *
        buildingLatticeGenerator P .three (u 1)) *
          buildingLatticeGenerator P .three (u 2) := by
  rw [list_ofFn_rankThree_local u]
  simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
private theorem buildingGeneratorWordProduct_rankFour_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorWordProduct P .four (List.ofFn u) =
      ((buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1)) *
          buildingLatticeGenerator P .four (u 2)) *
            buildingLatticeGenerator P .four (u 3) := by
  rw [list_ofFn_rankFour_local u]
  simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
private theorem buildingGeneratorPrefixProduct_rankThree_one_local
    (P : BasePrime) (u : Fin 3 → ConstantProjectiveClass P .three) :
    buildingGeneratorPrefixProduct P .three 1 u =
      buildingLatticeGenerator P .three (u 0) := by
  have htake : (List.ofFn u).take 1 = [u 0] := by
    rw [list_ofFn_rankThree_local u]
    rfl
  change buildingGeneratorWordProduct P .three ((List.ofFn u).take 1) = _
  calc
    buildingGeneratorWordProduct P .three ((List.ofFn u).take 1) =
        buildingGeneratorWordProduct P .three [u 0] :=
      congrArg (buildingGeneratorWordProduct P .three) htake
    _ = buildingLatticeGenerator P .three (u 0) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
private theorem buildingGeneratorPrefixProduct_rankThree_two_local
    (P : BasePrime) (u : Fin 3 → ConstantProjectiveClass P .three) :
    buildingGeneratorPrefixProduct P .three 2 u =
      buildingLatticeGenerator P .three (u 0) *
        buildingLatticeGenerator P .three (u 1) := by
  have htake : (List.ofFn u).take 2 = [u 0, u 1] := by
    rw [list_ofFn_rankThree_local u]
    rfl
  change buildingGeneratorWordProduct P .three ((List.ofFn u).take 2) = _
  calc
    buildingGeneratorWordProduct P .three ((List.ofFn u).take 2) =
        buildingGeneratorWordProduct P .three [u 0, u 1] :=
      congrArg (buildingGeneratorWordProduct P .three) htake
    _ = buildingLatticeGenerator P .three (u 0) *
        buildingLatticeGenerator P .three (u 1) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
private theorem buildingGeneratorPrefixProduct_rankFour_one_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorPrefixProduct P .four 1 u =
      buildingLatticeGenerator P .four (u 0) := by
  have htake : (List.ofFn u).take 1 = [u 0] := by
    rw [list_ofFn_rankFour_local u]
    rfl
  change buildingGeneratorWordProduct P .four ((List.ofFn u).take 1) = _
  calc
    buildingGeneratorWordProduct P .four ((List.ofFn u).take 1) =
        buildingGeneratorWordProduct P .four [u 0] :=
      congrArg (buildingGeneratorWordProduct P .four) htake
    _ = buildingLatticeGenerator P .four (u 0) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
private theorem buildingGeneratorPrefixProduct_rankFour_two_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorPrefixProduct P .four 2 u =
      buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1) := by
  have htake : (List.ofFn u).take 2 = [u 0, u 1] := by
    rw [list_ofFn_rankFour_local u]
    rfl
  change buildingGeneratorWordProduct P .four ((List.ofFn u).take 2) = _
  calc
    buildingGeneratorWordProduct P .four ((List.ofFn u).take 2) =
        buildingGeneratorWordProduct P .four [u 0, u 1] :=
      congrArg (buildingGeneratorWordProduct P .four) htake
    _ = buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
private theorem buildingGeneratorPrefixProduct_rankFour_three_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorPrefixProduct P .four 3 u =
      (buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1)) *
          buildingLatticeGenerator P .four (u 2) := by
  have htake : (List.ofFn u).take 3 = [u 0, u 1, u 2] := by
    rw [list_ofFn_rankFour_local u]
    rfl
  change buildingGeneratorWordProduct P .four ((List.ofFn u).take 3) = _
  calc
    buildingGeneratorWordProduct P .four ((List.ofFn u).take 3) =
        buildingGeneratorWordProduct P .four [u 0, u 1, u 2] :=
      congrArg (buildingGeneratorWordProduct P .four) htake
    _ = (buildingLatticeGenerator P .four (u 0) *
          buildingLatticeGenerator P .four (u 1)) *
        buildingLatticeGenerator P .four (u 2) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, mul_assoc]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingVertexDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r)
    {color : Nat} (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    (buildingGeneratorPrefixProduct P r color u).1 ∈
      fundamentalDoubleCoset (BaseField P) r.matrixRank color := by
  classical
  have hrel : buildingGeneratorWordProduct P r (List.ofFn u) = 1 := by
    have hu' := hu
    rw [buildingRelationTupleFinset, Finset.mem_filter] at hu'
    exact hu'.2
  cases r with
  | three =>
      change Fin 3 → ConstantProjectiveClass P .three at u
      simp only [Rank.matrixRank] at hcolor ⊢
      simp only [Finset.mem_Icc] at hcolor
      have hcases : color = 1 ∨ color = 2 := by omega
      rcases hcases with rfl | rfl
      · rw [buildingGeneratorPrefixProduct_rankThree_one_local P u]
        exact buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
          P .three (u 0)
      · have hrel' :
            (buildingLatticeGenerator P .three (u 0) *
              buildingLatticeGenerator P .three (u 1)) *
                buildingLatticeGenerator P .three (u 2) = 1 := by
            exact (buildingGeneratorWordProduct_rankThree_local P u).symm.trans hrel
        have hprefix :
            buildingLatticeGenerator P .three (u 0) *
                buildingLatticeGenerator P .three (u 1) =
              (buildingLatticeGenerator P .three (u 2))⁻¹ := by
          calc
            buildingLatticeGenerator P .three (u 0) *
                buildingLatticeGenerator P .three (u 1) =
              ((buildingLatticeGenerator P .three (u 0) *
                buildingLatticeGenerator P .three (u 1)) *
                  buildingLatticeGenerator P .three (u 2)) *
                (buildingLatticeGenerator P .three (u 2))⁻¹ := by group
            _ = (buildingLatticeGenerator P .three (u 2))⁻¹ := by
              rw [hrel', one_mul]
        rw [buildingGeneratorPrefixProduct_rankThree_two_local P u]
        rw [hprefix]
        have hinv :
            (buildingLatticeGenerator P .three (u 2)).1⁻¹ ∈
              (fundamentalDoubleCoset (BaseField P) 3 1)⁻¹ :=
          Set.inv_mem_inv.mpr
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .three (u 2))
        rw [fundamentalDoubleCoset_rankThree_one_inv] at hinv
        exact hinv
  | four =>
      change Fin 4 → ConstantProjectiveClass P .four at u
      simp only [Rank.matrixRank] at hcolor ⊢
      simp only [Finset.mem_Icc] at hcolor
      have hcases : color = 1 ∨ color = 2 ∨ color = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · rw [buildingGeneratorPrefixProduct_rankFour_one_local P u]
        exact buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
          P .four (u 0)
      · have hrel' :
            ((buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2)) *
                  buildingLatticeGenerator P .four (u 3) = 1 := by
            exact (buildingGeneratorWordProduct_rankFour_local P u).symm.trans hrel
        rw [buildingGeneratorPrefixProduct_rankFour_two_local P u]
        exact rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation P
            (buildingLatticeGenerator P .four (u 0))
            (buildingLatticeGenerator P .four (u 1))
            (buildingLatticeGenerator P .four (u 2))
            (buildingLatticeGenerator P .four (u 3))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 0))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 1))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 2))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 3)) hrel'
      · have hrel' :
            ((buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2)) *
                  buildingLatticeGenerator P .four (u 3) = 1 := by
            exact (buildingGeneratorWordProduct_rankFour_local P u).symm.trans hrel
        have hprefix :
            (buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2) =
              (buildingLatticeGenerator P .four (u 3))⁻¹ := by
          calc
            (buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2) =
              (((buildingLatticeGenerator P .four (u 0) *
                buildingLatticeGenerator P .four (u 1)) *
                  buildingLatticeGenerator P .four (u 2)) *
                    buildingLatticeGenerator P .four (u 3)) *
                (buildingLatticeGenerator P .four (u 3))⁻¹ := by group
            _ = (buildingLatticeGenerator P .four (u 3))⁻¹ := by
              rw [hrel', one_mul]
        rw [buildingGeneratorPrefixProduct_rankFour_three_local P u]
        rw [hprefix]
        have hinv :
            (buildingLatticeGenerator P .four (u 3)).1⁻¹ ∈
              (fundamentalDoubleCoset (BaseField P) 4 1)⁻¹ :=
          Set.inv_mem_inv.mpr
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 3))
        rw [fundamentalDoubleCoset_rankFour_one_inv] at hinv
        exact hinv
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
