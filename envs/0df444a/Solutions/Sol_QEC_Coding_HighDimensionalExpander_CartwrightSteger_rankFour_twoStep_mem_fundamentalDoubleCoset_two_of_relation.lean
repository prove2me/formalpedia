-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:44:09.649073+00:00
-- url     : https://prove2.me/submissions/61edbc19-58d3-4a78-955d-d014121363f0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_det_localUnitOrder
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_fundamental
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_mem_projectiveDominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalNeighborAdjacentEquiv_apply_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinear_det_localUnitOrder_eq_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationCoweight_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationGeneralLinear_conj_diagonal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_fundamental
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeBuildingAdjacencyFamily_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_subgroup_doubleCoset_inv_eq_of_inv_eq_conj
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
private theorem dominant_mem_fundamental_mul_of_common_member
    (P : BasePrime) (w : ProjectiveDominantCoweight 3)
    (x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hxw : x ∈ projectiveDominantDoubleCoset (BaseField P) w)
    (hxprod : x ∈ fundamentalDoubleCoset (BaseField P) 4 1 *
      fundamentalDoubleCoset (BaseField P) 4 1) :
    dominantCoweight (BaseField P) w.toDominant ∈
      projectiveDominantDoubleCoset (BaseField P)
          (fundamentalProjectiveDominantCoweight 3 1 (by omega)) *
        projectiveDominantDoubleCoset (BaseField P)
          (fundamentalProjectiveDominantCoweight 3 1 (by omega)) := by
  rw [projectiveDominantDoubleCoset_fundamental]
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset, Set.mem_mul] at hxw
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hxw
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  rw [Set.mem_mul] at hxprod ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := hxprod
  refine ⟨left⁻¹ * a,
    left_mul_mem_fundamentalDoubleCoset (BaseField P) 4 1
      ((maximalCompact (BaseField P) 4).inv_mem hleft) ha,
    b * right⁻¹,
    right_mul_mem_fundamentalDoubleCoset (BaseField P) 4 1
      ((maximalCompact (BaseField P) 4).inv_mem hright) hb, ?_⟩
  calc
    left⁻¹ * a * (b * right⁻¹) = left⁻¹ * (a * b) * right⁻¹ := by group
    _ = left⁻¹ * x * right⁻¹ := by rw [hab]
    _ = left⁻¹ * (middle * right) * right⁻¹ := by rw [← hfactor]
    _ = left⁻¹ * (left * dominantCoweight (BaseField P) w.toDominant) *
        right * right⁻¹ := by simp only [← hmiddleFactor, mul_assoc]
    _ = dominantCoweight (BaseField P) w.toDominant := by group
private theorem lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
    (P : BasePrime) (r : Rank)
    (x : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hx : x ∈ maximalCompact (BaseField P) r.matrixRank) :
    lsvProjectiveDetOrderColor P r x = 1 := by
  rw [mem_maximalCompact_iff] at hx
  obtain ⟨A, rfl⟩ := hx
  change lsvProjectiveDetOrderColor P r
      (Matrix.ProjGenLinGroup.mk
        (integralGeneralLinearToLocal (BaseField P) r.matrixRank A)) = 1
  rw [lsvProjectiveDetOrderColor_mk]
  change Multiplicative.ofAdd
      (localUnitOrder (Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal (BaseField P) r.matrixRank A)) :
        ZMod r.matrixRank) = 1
  rw [integralGeneralLinear_det_localUnitOrder_eq_zero]
  simp
private theorem lsvProjectiveDetOrderColor_of_mem_rankFour_one
    (P : BasePrime)
    (x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hx : x ∈ fundamentalDoubleCoset (BaseField P) 4 1) :
    lsvProjectiveDetOrderColor P .four x =
      Multiplicative.ofAdd (1 : ZMod 4) := by
  rw [fundamentalDoubleCoset, Set.mem_mul] at hx
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hx
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  rw [← hfactor, ← hmiddleFactor]
  have hmapOuter := (lsvProjectiveDetOrderColor P .four).map_mul
    (left * fundamentalCoweight (BaseField P) 4 1) right
  have hmapInner := (lsvProjectiveDetOrderColor P .four).map_mul
    left (fundamentalCoweight (BaseField P) 4 1)
  calc
    lsvProjectiveDetOrderColor P .four
        (left * fundamentalCoweight (BaseField P) 4 1 * right) =
        lsvProjectiveDetOrderColor P .four
            (left * fundamentalCoweight (BaseField P) 4 1) *
          lsvProjectiveDetOrderColor P .four right := hmapOuter
    _ = (lsvProjectiveDetOrderColor P .four left *
          lsvProjectiveDetOrderColor P .four
            (fundamentalCoweight (BaseField P) 4 1)) *
        lsvProjectiveDetOrderColor P .four right :=
      congrArg (fun z => z * lsvProjectiveDetOrderColor P .four right) hmapInner
    _ = lsvProjectiveDetOrderColor P .four
        (fundamentalCoweight (BaseField P) 4 1) := by
      rw [lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four left hleft,
        lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four right hright, one_mul, mul_one]
    _ = Multiplicative.ofAdd (1 : ZMod Rank.four.matrixRank) := by
      change lsvProjectiveDetOrderColor P .four
          (Matrix.ProjGenLinGroup.mk
            (fundamentalDiagonal (BaseField P) 4 1)) = _
      erw [lsvProjectiveDetOrderColor_mk]
      change Multiplicative.ofAdd
          (localUnitOrder (Matrix.GeneralLinearGroup.det
            (fundamentalDiagonal (BaseField P) 4 1)) : ZMod 4) = _
      rw [show fundamentalDiagonal (BaseField P) 4 1 =
          dominantGeneralLinear (BaseField P)
            (fundamentalDominantCoweight 4 1) by
        symm
        exact dominantGeneralLinear_fundamental (BaseField P) 4 1]
      rw [dominantGeneralLinear_det_localUnitOrder]
      norm_num [fundamentalDominantCoweight, Fin.sum_univ_succ]
      rfl
private theorem lsvProjectiveDetOrderColor_of_mem_projectiveDominantDoubleCoset
    (P : BasePrime) (w : ProjectiveDominantCoweight 3)
    (x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hx : x ∈ projectiveDominantDoubleCoset (BaseField P) w) :
    lsvProjectiveDetOrderColor P .four x =
      Multiplicative.ofAdd
        ((∑ i, w.toDominant.exponent i : Nat) : ZMod 4) := by
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset, Set.mem_mul] at hx
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hx
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  rw [← hfactor, ← hmiddleFactor]
  have hmapOuter := (lsvProjectiveDetOrderColor P .four).map_mul
    (left * dominantCoweight (BaseField P) w.toDominant) right
  have hmapInner := (lsvProjectiveDetOrderColor P .four).map_mul
    left (dominantCoweight (BaseField P) w.toDominant)
  calc
    lsvProjectiveDetOrderColor P .four
        (left * dominantCoweight (BaseField P) w.toDominant * right) =
        lsvProjectiveDetOrderColor P .four
            (left * dominantCoweight (BaseField P) w.toDominant) *
          lsvProjectiveDetOrderColor P .four right := hmapOuter
    _ = (lsvProjectiveDetOrderColor P .four left *
          lsvProjectiveDetOrderColor P .four
            (dominantCoweight (BaseField P) w.toDominant)) *
        lsvProjectiveDetOrderColor P .four right :=
      congrArg (fun z => z * lsvProjectiveDetOrderColor P .four right) hmapInner
    _ = lsvProjectiveDetOrderColor P .four
        (dominantCoweight (BaseField P) w.toDominant) := by
      rw [lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four left hleft,
        lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four right hright, one_mul, mul_one]
    _ = Multiplicative.ofAdd
        ((∑ i, w.toDominant.exponent i : Nat) : ZMod Rank.four.matrixRank) := by
      change lsvProjectiveDetOrderColor P .four
          (Matrix.ProjGenLinGroup.mk
            (dominantGeneralLinear (BaseField P) w.toDominant)) = _
      rw [lsvProjectiveDetOrderColor_mk]
      change Multiplicative.ofAdd
          (localUnitOrder (Matrix.GeneralLinearGroup.det
            (dominantGeneralLinear (BaseField P) w.toDominant)) :
            ZMod 4) = _
      rw [dominantGeneralLinear_det_localUnitOrder]
      rfl
private theorem rankFour_weight_sum_two_cases
    (w : ProjectiveDominantCoweight 3)
    (hsum : ∑ i, w.toDominant.exponent i = 2) :
    w = fundamentalProjectiveDominantCoweight 3 2 (by omega) ∨
      w = rankFourDoubleFirstWeight := by
  have hlast : w.toDominant.exponent (3 : Fin 4) = 0 := by
    simpa using w.last_exponent_eq_zero
  have h01 := w.toDominant.antitone_exponent
    (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := w.toDominant.antitone_exponent
    (show (1 : Fin 4) ≤ 2 by decide)
  simp [Fin.sum_univ_succ, hlast] at hsum
  by_cases hfirst : w.toDominant.exponent (0 : Fin 4) = 1
  · left
    apply ProjectiveDominantCoweight.ext
    funext i
    fin_cases i <;>
      simp [fundamentalProjectiveDominantCoweight,
        fundamentalDominantCoweight, hfirst, hlast] <;> omega
  · right
    apply ProjectiveDominantCoweight.ext
    funext i
    fin_cases i <;>
      simp [rankFourDoubleFirstWeight, hlast] <;> omega
private theorem rankFourDoubleFirstWeight_inv
    (P : BasePrime) :
    (projectiveDominantDoubleCoset (BaseField P)
      rankFourDoubleFirstWeight)⁻¹ =
      projectiveDominantDoubleCoset (BaseField P)
        rankFourDoubleFirstInverseWeight := by
  rw [projectiveDominantDoubleCoset, projectiveDominantDoubleCoset]
  apply subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact (BaseField P) 4)
    (permutationCoweight_mem_maximalCompact (BaseField P) Fin.revPerm)
  have hscalar :
      Matrix.GeneralLinearGroup.scalar (Fin 4)
          (uniformizerUnit (BaseField P) ^ 2) *
        (dominantGeneralLinear (BaseField P)
          rankFourDoubleFirstWeight.toDominant)⁻¹ =
      permutationGeneralLinear (BuildingLocalField P) Fin.revPerm *
        dominantGeneralLinear (BaseField P)
          rankFourDoubleFirstInverseWeight.toDominant *
        (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm)⁻¹ := by
    change _ = permutationGeneralLinear (BuildingLocalField P) Fin.revPerm *
      diagonalGeneralLinear (BuildingLocalField P) 4
        (fun i => uniformizerUnit (BaseField P) ^
          rankFourDoubleFirstInverseWeight.toDominant.exponent i) *
      (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm)⁻¹
    rw [permutationGeneralLinear_conj_diagonal]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rankFourDoubleFirstWeight, rankFourDoubleFirstInverseWeight,
        dominantGeneralLinear, diagonalGeneralLinear_inv,
        diagonalGeneralLinear_apply, Matrix.mul_apply, pow_two]
  have hmk := congrArg Matrix.ProjGenLinGroup.mk hscalar
  change
    Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.scalar (Fin 4)
          (uniformizerUnit (BaseField P) ^ 2)) *
          (dominantCoweight (BaseField P)
            rankFourDoubleFirstWeight.toDominant)⁻¹ =
      Matrix.ProjGenLinGroup.mk
          (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm) *
        dominantCoweight (BaseField P)
          rankFourDoubleFirstInverseWeight.toDominant *
        (Matrix.ProjGenLinGroup.mk
          (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm))⁻¹ at hmk
  simp [Matrix.ProjGenLinGroup.mk_scalar] at hmk ⊢
  exact hmk
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
    (P : BasePrime)
    (a b c d : BuildingCartwrightStegerLattice P .four)
    (ha : a.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hb : b.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hc : c.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hd : d.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hprod : ((a * b) * c) * d = 1) :
    (a * b).1 ∈ fundamentalDoubleCoset (BaseField P) 4 2 := by
  let x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P) := (a * b).1
  have hxprod : x ∈ fundamentalDoubleCoset (BaseField P) 4 1 *
      fundamentalDoubleCoset (BaseField P) 4 1 := by
    rw [Set.mem_mul]
    exact ⟨a.1, ha, b.1, hb, rfl⟩
  obtain ⟨w, hxw⟩ := exists_mem_projectiveDominantDoubleCoset
    (BaseField P) x
  have hdiagprod := dominant_mem_fundamental_mul_of_common_member P w x hxw hxprod
  let f1 := fundamentalProjectiveDominantCoweight 3 1 (by omega)
  have hsumInt := projectiveDominant_exponent_sum_le_of_mem_cartanDoubleCoset_mul
    (BaseField P) w f1 f1 hdiagprod
  have hsumLe : (∑ i, w.toDominant.exponent i) ≤ 2 := by
    exact_mod_cast hsumInt
  have hxcolor : lsvProjectiveDetOrderColor P .four x =
      Multiplicative.ofAdd (2 : ZMod 4) := by
    change lsvBuildingLatticeColor P .four (a * b) = _
    rw [map_mul]
    change lsvBuildingLatticeColor P .four a *
      lsvBuildingLatticeColor P .four b = _
    have haColor := lsvProjectiveDetOrderColor_of_mem_rankFour_one P a.1 ha
    have hbColor := lsvProjectiveDetOrderColor_of_mem_rankFour_one P b.1 hb
    change lsvProjectiveDetOrderColor P .four a.1 *
      lsvProjectiveDetOrderColor P .four b.1 = _
    rw [haColor, hbColor]
    apply Multiplicative.toAdd.injective
    change (1 : ZMod 4) + 1 = 2
    norm_num
  have hwcolor :=
    lsvProjectiveDetOrderColor_of_mem_projectiveDominantDoubleCoset
      P w x hxw
  have hsumZMod :
      (((∑ i, w.toDominant.exponent i : Nat) : ZMod 4)) = 2 := by
    apply Multiplicative.ofAdd.injective
    exact hwcolor.symm.trans hxcolor
  have hsum : ∑ i, w.toDominant.exponent i = 2 := by
    let s := ∑ i, w.toDominant.exponent i
    have hs : s ≤ 2 := by simpa [s] using hsumLe
    change (s : ZMod 4) = 2 at hsumZMod
    change s = 2
    interval_cases hsval : s
    · exfalso
      exact (by decide : (0 : ZMod 4) ≠ 2) hsumZMod
    · exfalso
      exact (by decide : (1 : ZMod 4) ≠ 2) hsumZMod
    · rfl
  rcases rankFour_weight_sum_two_cases w hsum with hw | hw
  · rw [hw, projectiveDominantDoubleCoset_fundamental] at hxw
    exact hxw
  · subst w
    exfalso
    have hxinvBad : x⁻¹ ∈ projectiveDominantDoubleCoset (BaseField P)
        rankFourDoubleFirstInverseWeight := by
      have hinvset : x⁻¹ ∈
          (projectiveDominantDoubleCoset (BaseField P)
            rankFourDoubleFirstWeight)⁻¹ := by
        exact Set.inv_mem_inv.mpr hxw
      rw [rankFourDoubleFirstWeight_inv P] at hinvset
      exact hinvset
    have hxinvProd : x⁻¹ ∈ fundamentalDoubleCoset (BaseField P) 4 1 *
        fundamentalDoubleCoset (BaseField P) 4 1 := by
      have hxcd : x⁻¹ = c.1 * d.1 := by
        change ((a * b).1)⁻¹ = (c * d).1
        have hprodGrouped : (a * b) * (c * d) = 1 := by
          simpa only [mul_assoc] using hprod
        have hprod'' := congrArg Subtype.val hprodGrouped
        exact inv_eq_of_mul_eq_one_right hprod''
      rw [hxcd]
      erw [Set.mem_mul]
      exact ⟨c.1, hc, d.1, hd, rfl⟩
    have hdiagInvProd := dominant_mem_fundamental_mul_of_common_member
      P rankFourDoubleFirstInverseWeight x⁻¹ hxinvBad hxinvProd
    have hbadBound := projectiveDominant_exponent_sum_le_of_mem_cartanDoubleCoset_mul
      (BaseField P) rankFourDoubleFirstInverseWeight f1 f1 hdiagInvProd
    norm_num [rankFourDoubleFirstInverseWeight, f1,
      fundamentalProjectiveDominantCoweight, fundamentalDominantCoweight,
      Fin.sum_univ_succ] at hbadBound
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
