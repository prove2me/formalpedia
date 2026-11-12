-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCartwrightStegerLattice_stabilizer_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:15:24.77706+00:00
-- url     : https://prove2.me/submissions/282087f2-fce6-46d7-88fe-42ba0b493da5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitLattice_hasIdentityConjugationDiagonal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_orderUnitLattice_lift_of_buildingLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r)
    (hg : (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (BuildingLocalField P)) ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    g = 1 := by
  obtain ⟨u, hu, hmap⟩ :=
    exists_orderUnitLattice_lift_of_buildingLattice P r g
  have huCompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    rw [hmap]
    exact hg
  have huCyclic : orderUnitToBuildingPGL P r u ∈
      BuildingCompactCyclicSubgroup P r :=
    orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
      P r u huCompact
  have huDiag : BuildingElementHasIdentityConjugationDiagonal P r
      (orderUnitToBuildingPGL P r u) :=
    orderUnitLattice_hasIdentityConjugationDiagonal
      P r u hu huCompact
  have huOne : orderUnitToBuildingPGL P r u = 1 :=
    eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
      P r (orderUnitToBuildingPGL P r u) huCyclic huDiag
  apply Subtype.ext
  rw [← hmap]
  exact huOne
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
