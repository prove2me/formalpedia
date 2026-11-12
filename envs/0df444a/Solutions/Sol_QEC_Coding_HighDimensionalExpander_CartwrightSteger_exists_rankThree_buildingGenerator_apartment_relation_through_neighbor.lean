-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankThree_buildingGenerator_apartment_relation_through_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:23:15.38797+00:00
-- url     : https://prove2.me/submissions/ab1fa30e-7a5a-48e1-967a-e76ecc1747fc

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusY
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticRingToFunctionField_arithmeticOnePlusYInv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicElement_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerBCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_constantCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicMonomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_existsUnique_generator_mul_eq_coloredNeighbor
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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_rankThree_zero_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_zero_eq_fundamental
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerCoweight
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
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


section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.SphericalHecke
private theorem exists_compact_mul_fundamentalCoweight_mk_eq_of_mem_neighbor
    (P : BasePrime) (r : Rank) (color : Nat)
    (q : CartwrightStegerBuildingVertex P r)
    (hq : q ∈ fundamentalNeighborCosets
      (BaseField P) r.matrixRank color) :
    ∃ left : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P),
      left ∈ maximalCompact (BaseField P) r.matrixRank ∧
      QuotientGroup.mk
          (left * fundamentalCoweight (BaseField P) r.matrixRank color) = q := by
  rw [mem_fundamentalNeighborCosets] at hq
  obtain ⟨x, hx, hxq⟩ := hq
  rw [fundamentalDoubleCoset, Set.mem_mul] at hx
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hx
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  refine ⟨left, hleft, ?_⟩
  have hrightCoset :
      QuotientGroup.mk ((left *
          fundamentalCoweight (BaseField P) r.matrixRank color) * right) =
        (QuotientGroup.mk (left *
          fundamentalCoweight (BaseField P) r.matrixRank color) :
          CartwrightStegerBuildingVertex P r) := by
    apply QuotientGroup.eq.mpr
    simpa [mul_assoc] using
      (maximalCompact (BaseField P) r.matrixRank).inv_mem hright
  rw [← hxq, ← hfactor, ← hmiddleFactor, hrightCoset]
private theorem translatedRankThreeAdjacent01
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 3) :
    ColoredBuildingAdjacent (BaseField P) 3 1
      (QuotientGroup.mk 1) (translatedRankThreeVertex1 P left) := by
  rw [translatedRankThreeVertex1]
  change ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk 1)
    (QuotientGroup.mk (left *
      coordinateUniformizerCoweight (BaseField P) 3 0))
  rw [coloredBuildingAdjacent_mk_iff]
  simp only [inv_one, one_mul]
  change left * coordinateUniformizerCoweight (BaseField P) 3 0 ∈
    fundamentalDoubleCoset (BaseField P) 3 1
  exact left_mul_mem_fundamentalDoubleCoset (BaseField P) 3 1 hleft
    (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
      (BaseField P) (by omega) 0)
private theorem translatedRankThreeAdjacent12
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P)) :
    ColoredBuildingAdjacent (BaseField P) 3 1
      (translatedRankThreeVertex1 P left)
      (translatedRankThreeVertex2 P left) := by
  rw [translatedRankThreeVertex1, translatedRankThreeVertex2]
  change ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk (left *
      coordinateUniformizerCoweight (BaseField P) 3 0))
    (QuotientGroup.mk ((left *
      coordinateUniformizerCoweight (BaseField P) 3 0) *
        coordinateUniformizerCoweight (BaseField P) 3 1))
  rw [coloredBuildingAdjacent_mk_iff]
  change (left * coordinateUniformizerCoweight (BaseField P) 3 0)⁻¹ *
      ((left * coordinateUniformizerCoweight (BaseField P) 3 0) *
        coordinateUniformizerCoweight (BaseField P) 3 1) ∈
    fundamentalDoubleCoset (BaseField P) 3 1
  simpa [mul_assoc] using
    (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
      (BaseField P) (by omega) (1 : Fin 3))
private theorem translatedRankThreeAdjacent20
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 3) :
    ColoredBuildingAdjacent (BaseField P) 3 1
      (translatedRankThreeVertex2 P left) (QuotientGroup.mk 1) := by
  let c0 := coordinateUniformizerCoweight (BaseField P) 3 (0 : Fin 3)
  let c1 := coordinateUniformizerCoweight (BaseField P) 3 (1 : Fin 3)
  let c2 := coordinateUniformizerCoweight (BaseField P) 3 (2 : Fin 3)
  have hstep : ColoredBuildingAdjacent (BaseField P) 3 1
      (QuotientGroup.mk ((left * c0) * c1))
      (QuotientGroup.mk (((left * c0) * c1) * c2)) := by
    rw [coloredBuildingAdjacent_mk_iff]
    simpa [mul_assoc] using
      (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
        (BaseField P) (by omega) (2 : Fin 3))
  have hcycle : c0 * c1 * c2 = 1 := by
    have h := prod_coordinateUniformizerCoweight (BaseField P) 3
    norm_num [List.finRange] at h
    simpa [c0, c1, c2, mul_assoc] using h
  have hend :
      (QuotientGroup.mk (((left * c0) * c1) * c2) :
          CartwrightStegerBuildingVertex P .three) = QuotientGroup.mk 1 := by
    rw [show ((left * c0) * c1) * c2 = left * (c0 * c1 * c2) by group,
      hcycle, mul_one]
    apply QuotientGroup.eq.mpr
    rw [mul_one]
    exact (maximalCompact (BaseField P) 3).inv_mem hleft
  rw [translatedRankThreeVertex2]
  change ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk ((left * c0) * c1)) (QuotientGroup.mk 1)
  exact hend ▸ hstep
private theorem exists_translated_rankThree_apartment_relation
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 3) :
    ∃ u0 u1 u2 : ConstantProjectiveClass P .three,
      buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1 *
            buildingLatticeGenerator P .three u2 = 1 ∧
      buildingLatticeVertexMap P .three
          (buildingLatticeGenerator P .three u0) =
        QuotientGroup.mk (left * fundamentalCoweight (BaseField P) 3 1) ∧
      buildingLatticeVertexMap P .three
          (buildingLatticeGenerator P .three u0 *
            buildingLatticeGenerator P .three u1) =
        QuotientGroup.mk (left * fundamentalCoweight (BaseField P) 3 2) := by
  let v1 := translatedRankThreeVertex1 P left
  let v2 := translatedRankThreeVertex2 P left
  let u0 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three 1 v1 (by
      rw [buildingLatticeVertexMap_one]
      exact translatedRankThreeAdjacent01 P left hleft))
  have hu0 : buildingLatticeVertexMap P .three
      (1 * buildingLatticeGenerator P .three u0) = v1 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .three 1 v1 (by
        rw [buildingLatticeVertexMap_one]
        exact translatedRankThreeAdjacent01 P left hleft))).1
  let u1 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three (1 * buildingLatticeGenerator P .three u0) v2 (by
      rw [hu0]
      exact translatedRankThreeAdjacent12 P left))
  have hu01 : buildingLatticeVertexMap P .three
      ((1 * buildingLatticeGenerator P .three u0) *
        buildingLatticeGenerator P .three u1) = v2 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .three (1 * buildingLatticeGenerator P .three u0) v2 (by
        rw [hu0]
        exact translatedRankThreeAdjacent12 P left))).1
  let u2 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three ((1 * buildingLatticeGenerator P .three u0) *
      buildingLatticeGenerator P .three u1) (QuotientGroup.mk 1) (by
        rw [hu01]
        exact translatedRankThreeAdjacent20 P left hleft))
  have hu012 : buildingLatticeVertexMap P .three
      (((1 * buildingLatticeGenerator P .three u0) *
        buildingLatticeGenerator P .three u1) *
          buildingLatticeGenerator P .three u2) = QuotientGroup.mk 1 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .three ((1 * buildingLatticeGenerator P .three u0) *
        buildingLatticeGenerator P .three u1) (QuotientGroup.mk 1) (by
          rw [hu01]
          exact translatedRankThreeAdjacent20 P left hleft))).1
  refine ⟨u0, u1, u2, ?_, ?_, ?_⟩
  · apply buildingLatticeVertexMap_injective P .three
    simp only [one_mul] at hu012
    exact hu012
  · rw [one_mul] at hu0
    dsimp [v1, translatedRankThreeVertex1] at hu0
    have hc0 : coordinateUniformizerCoweight (BaseField P) 3 (0 : Fin 3) =
        fundamentalCoweight (BaseField P) 3 1 := by
      exact coordinateUniformizerCoweight_zero_eq_fundamental
        (BaseField P) (d := 3) (by omega)
    rw [hc0] at hu0
    exact hu0
  · rw [one_mul] at hu01
    dsimp [v2, translatedRankThreeVertex2] at hu01
    rw [mul_assoc, coordinateUniformizerCoweight_rankThree_zero_one] at hu01
    exact hu01
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.SphericalHecke
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (color : Fin 2)
    (q : CartwrightStegerBuildingVertex P .three)
    (hq : q ∈ fundamentalNeighborCosets (BaseField P) 3 (color.val + 1)) :
    ∃ u0 u1 u2 : ConstantProjectiveClass P .three,
      buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1 *
            buildingLatticeGenerator P .three u2 = 1 ∧
      (buildingLatticeGenerator P .three u0).1 ∈
        fundamentalDoubleCoset (BaseField P) 3 1 ∧
      (buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1).1 ∈
        fundamentalDoubleCoset (BaseField P) 3 2 ∧
      buildingLatticeVertexMap P .three
        (if color = 0 then buildingLatticeGenerator P .three u0
          else buildingLatticeGenerator P .three u0 *
            buildingLatticeGenerator P .three u1) = q := by
  obtain ⟨left, hleft, hqleft⟩ :=
    exists_compact_mul_fundamentalCoweight_mk_eq_of_mem_neighbor
      P .three (color.val + 1) q hq
  obtain ⟨u0, u1, u2, hrel, hprefix1, hprefix2⟩ :=
    exists_translated_rankThree_apartment_relation P left hleft
  have hmem1 :=
    buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
      P .three 1 (buildingLatticeGenerator P .three u0) left hleft hprefix1
  have hmem2 :=
    buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
      P .three 2 (buildingLatticeGenerator P .three u0 *
        buildingLatticeGenerator P .three u1) left hleft hprefix2
  refine ⟨u0, u1, u2, hrel, hmem1, hmem2, ?_⟩
  fin_cases color
  · simpa using hprefix1.trans hqleft
  · simpa using hprefix2.trans hqleft
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
