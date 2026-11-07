-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:52:11.598229+00:00
-- url     : https://prove2.me/submissions/99af183d-af06-4be4-a5db-cab4c4003c90

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (g h : BuildingCartwrightStegerLattice P r) :
    buildingLatticeVertexMap P r g = buildingLatticeVertexMap P r h ↔
      ((g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P))⁻¹ *
        (h : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P))) ∈
        SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
  exact QuotientGroup.eq
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
