-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitLattice_hasIdentityConjugationDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:12:37.873283+00:00
-- url     : https://prove2.me/submissions/9764ad41-28e3-4254-832b-a8fd13ff4ad1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_hasUpperUnipotentInfinityResidue_of_projective_mk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_compactNormalForm_hasIdentityDiagonal_of_upperResidue
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderUnitLattice_to_global


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ)
    (hu : u ∈ CartwrightStegerOrderUnitLattice P r)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    BuildingElementHasIdentityConjugationDiagonal P r
      (orderUnitToBuildingPGL P r u) := by
  intro c j hj hbuilding
  have hglobal :=
    orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
      P r u hcompact c j hbuilding
  have hglobalMem : orderUnitToGlobalGL P r u ∈
      CartwrightStegerMatrixGroup P r := by
    have hmap : orderUnitToGlobalGL P r u ∈
        (CartwrightStegerOrderUnitLattice P r).map
          (orderUnitToGlobalGL P r) := ⟨u, hu, rfl⟩
    rw [map_orderUnitLattice_to_global] at hmap
    exact hmap
  have hupperUnit : HasUpperUnipotentInfinityResidue P r
      (orderUnitToGlobalGL P r u) :=
    cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
      P r hglobalMem
  have hupperNormal : HasUpperUnipotentInfinityResidue P r
      (globalCompactNormalForm P r c j) := by
    apply hasUpperUnipotentInfinityResidue_of_projective_mk_eq
      P r hupperUnit
    exact hglobal
  exact compactNormalForm_hasIdentityDiagonal_of_upperResidue
    P r c j hupperNormal
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
