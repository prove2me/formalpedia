-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvThreeDimensionalQuotient_tetrahedronFaces_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:30:43.140497+00:00
-- url     : https://prove2.me/submissions/78d7a8a8-ba51-4d08-bfe8-3fb1d494668a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_bundledIndexGenerator_ne_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankFour_bundledIndexGenerator_mul_ne_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingRelationTupleFinset_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexGeneratorRotatedPrefix_mem_color
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexColorGeneratorFinset_subset_colored
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexClassGenerator_wordProduct_eq_one_of_building_relation
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CayleyClique_quadruple_mem_cliqueComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
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
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
private theorem coe_indexGeneratorWordProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r)) :
    ((indexGeneratorWordProduct P r level word : IndexFiniteGroup P r level) :
        PGL P r level) =
      (word.map (indexCartwrightStegerClassGenerator P r level)).prod := by
  induction word with
  | nil => rfl
  | cons u word ih =>
      simp only [indexGeneratorWordProduct, List.map_cons, List.prod_cons,
        Subgroup.coe_mul, coe_bundledIndexGenerator]
      simpa [indexGeneratorWordProduct] using congrArg
        (fun g => indexCartwrightStegerClassGenerator P r level u * g) ih
private theorem indexGeneratorWordProduct_eq_one_of_classProduct_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r))
    (h : (word.map
      (indexCartwrightStegerClassGenerator P r level)).prod = 1) :
    indexGeneratorWordProduct P r level word = 1 := by
  apply Subtype.ext
  rw [coe_indexGeneratorWordProduct]
  exact h
private theorem indexGeneratorWordProduct_eq_one_of_building_relation
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r))
    (hbuilding : (word.map (buildingLatticeGenerator P r)).prod = 1) :
    indexGeneratorWordProduct P r level word = 1 := by
  apply indexGeneratorWordProduct_eq_one_of_classProduct_eq_one
  exact indexClassGenerator_wordProduct_eq_one_of_building_relation
    P r level word hbuilding
private theorem list_ofFn_rankFour
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    List.ofFn u = [u rankFourIndexZero, u rankFourIndexOne,
      u rankFourIndexTwo, u rankFourIndexThree] := by
  change List.ofFn (fun i : Fin 4 => u i) = _
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl
private theorem rankFour_rotate_zero_take_one
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 1 = [u rankFourIndexZero] := by
  rw [list_ofFn_rankFour]
  rfl
private theorem rankFour_rotate_one_take_one
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 1).take 1 = [u rankFourIndexOne] := by
  rw [list_ofFn_rankFour]
  rfl
private theorem rankFour_rotate_two_take_one
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 2).take 1 = [u rankFourIndexTwo] := by
  rw [list_ofFn_rankFour]
  rfl
private theorem rankFour_rotate_zero_take_two
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 2 =
      [u rankFourIndexZero, u rankFourIndexOne] := by
  rw [list_ofFn_rankFour]
  rfl
private theorem rankFour_rotate_one_take_two
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 1).take 2 =
      [u rankFourIndexOne, u rankFourIndexTwo] := by
  rw [list_ofFn_rankFour]
  rfl
private theorem rankFour_rotate_zero_take_three
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 3 =
      [u rankFourIndexZero, u rankFourIndexOne, u rankFourIndexTwo] := by
  rw [list_ofFn_rankFour]
  rfl
section VertexFaces
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)
variable {K}
end VertexFaces
section CayleyFaceIncidence
universe u
variable {Γ : Type u} [Group Γ] [Fintype Γ] [DecidableEq Γ]
end CayleyFaceIncidence
section CofaceBounds
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : AbstractSimplicialComplex V} {p : Nat}
end CofaceBounds
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (level : Nat) :
    Nonempty
      (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) := by
  classical
  obtain ⟨u, hu⟩ := buildingRelationTupleFinset_nonempty P .four
  let a : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexZero)
  let b : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexOne)
  let c : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexTwo)
  let d : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexThree)
  let ab : IndexFiniteGroup P .four level := a * b
  let bc : IndexFiniteGroup P .four level := b * c
  let abc : IndexFiniteGroup P .four level := ab * c
  have hrelation : abc * d = 1 := by
    have hu' := hu
    rw [buildingRelationTupleFinset, Finset.mem_filter] at hu'
    have huProduct := indexGeneratorWordProduct_eq_one_of_building_relation
      P .four level (List.ofFn u) hu'.2
    rw [list_ofFn_rankFour] at huProduct
    change ((a * b) * c) * d = 1
    change a * (b * (c * (d * 1))) = 1 at huProduct
    simpa only [mul_one, mul_assoc] using huProduct
  have ha_ne : a ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexZero)
  have hb_ne : b ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexOne)
  have hc_ne : c ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexTwo)
  have hd_ne : d ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexThree)
  have hab_ne : ab ≠ 1 := by
    exact rankFour_bundledIndexGenerator_mul_ne_one P level
      (u rankFourIndexZero) (u rankFourIndexOne)
  have hbc_ne : bc ≠ 1 := by
    exact rankFour_bundledIndexGenerator_mul_ne_one P level
      (u rankFourIndexOne) (u rankFourIndexTwo)
  have habc_ne : abc ≠ 1 := by
    intro habc
    apply hd_ne
    rw [habc, one_mul] at hrelation
    exact hrelation
  have haColor : a ∈ indexColorGeneratorFinset P .four level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 0 1
    rw [rankFour_rotate_zero_take_one] at h
    simpa [indexGeneratorWordProduct, a] using h
  have hbColor : b ∈ indexColorGeneratorFinset P .four level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 1 1
    rw [rankFour_rotate_one_take_one] at h
    simpa [indexGeneratorWordProduct, b] using h
  have hcColor : c ∈ indexColorGeneratorFinset P .four level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 2 1
    rw [rankFour_rotate_two_take_one] at h
    simpa [indexGeneratorWordProduct, c] using h
  have habColor : ab ∈ indexColorGeneratorFinset P .four level 2 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 0 2
    rw [rankFour_rotate_zero_take_two] at h
    simpa [indexGeneratorWordProduct, a, b, ab] using h
  have hbcColor : bc ∈ indexColorGeneratorFinset P .four level 2 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 1 2
    rw [rankFour_rotate_one_take_two] at h
    simpa [indexGeneratorWordProduct, b, c, bc] using h
  have habcColor : abc ∈ indexColorGeneratorFinset P .four level 3 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 0 3
    rw [rankFour_rotate_zero_take_three] at h
    simpa [indexGeneratorWordProduct, a, b, c, ab, abc, mul_assoc] using h
  have h1 : 1 ∈ Finset.Icc 1 (Rank.four.matrixRank - 1) := by decide
  have h2 : 2 ∈ Finset.Icc 1 (Rank.four.matrixRank - 1) := by decide
  have h3 : 3 ∈ Finset.Icc 1 (Rank.four.matrixRank - 1) := by decide
  have haMem := indexColorGeneratorFinset_subset_colored
    P .four level 1 h1 haColor
  have hbMem := indexColorGeneratorFinset_subset_colored
    P .four level 1 h1 hbColor
  have hcMem := indexColorGeneratorFinset_subset_colored
    P .four level 1 h1 hcColor
  have habMem := indexColorGeneratorFinset_subset_colored
    P .four level 2 h2 habColor
  have hbcMem := indexColorGeneratorFinset_subset_colored
    P .four level 2 h2 hbcColor
  have habcMem := indexColorGeneratorFinset_subset_colored
    P .four level 3 h3 habcColor
  let G := SimpleGraph.mulCayley
    (indexColoredGeneratorFinset P .four level :
      Set (IndexFiniteGroup P .four level))
  have hadj_one_a : G.Adj 1 a := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨ha_ne.symm, Or.inl (by simpa using haMem)⟩
  have hadj_one_ab : G.Adj 1 ab := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨hab_ne.symm, Or.inl (by simpa using habMem)⟩
  have hadj_one_abc : G.Adj 1 abc := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨habc_ne.symm, Or.inl (by simpa using habcMem)⟩
  have ha_ab_ne : a ≠ ab :=
    ((mul_ne_left : a * b ≠ a ↔ b ≠ 1).mpr hb_ne).symm
  have ha_abc_ne : a ≠ abc := by
    have hmul : a * bc ≠ a :=
      (mul_ne_left : a * bc ≠ a ↔ bc ≠ 1).mpr hbc_ne
    have heq : abc = a * bc := by simp [abc, ab, bc, mul_assoc]
    rw [heq]
    exact hmul.symm
  have hab_abc_ne : ab ≠ abc :=
    ((mul_ne_left : ab * c ≠ ab ↔ c ≠ 1).mpr hc_ne).symm
  have hadj_a_ab : G.Adj a ab := by
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨ha_ab_ne, Or.inl ?_⟩
    change a⁻¹ * (a * b) ∈
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    rw [inv_mul_cancel_left]
    exact hbMem
  have hadj_a_abc : G.Adj a abc := by
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨ha_abc_ne, Or.inl ?_⟩
    change a⁻¹ * ((a * b) * c) ∈
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    rw [← mul_assoc, inv_mul_cancel_left]
    exact hbcMem
  have hadj_ab_abc : G.Adj ab abc := by
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨hab_abc_ne, Or.inl ?_⟩
    change ab⁻¹ * (ab * c) ∈
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    rw [inv_mul_cancel_left]
    exact hcMem
  refine ⟨⟨{1, a, ab, abc}, ?_, ?_⟩⟩
  · change {1, a, ab, abc} ∈ CayleyClique.cayleyCliqueComplex
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    exact CayleyClique.quadruple_mem_cliqueComplex G
      hadj_one_a hadj_one_ab hadj_one_abc
      hadj_a_ab hadj_a_abc hadj_ab_abc
  · exact Finset.card_eq_four.mpr
      ⟨1, a, ab, abc, ha_ne.symm, hab_ne.symm, habc_ne.symm,
        ha_ab_ne, ha_abc_ne, hab_abc_ne, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
