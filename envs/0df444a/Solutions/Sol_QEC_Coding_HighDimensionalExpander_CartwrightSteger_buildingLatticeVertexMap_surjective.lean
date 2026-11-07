-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:47.360639+00:00
-- url     : https://prove2.me/submissions/1d1b3e88-f322-46c4-adad-480aaeab8a66

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_lattice_of_colorOne_reachable
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFour_colorOneReachable
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThree_colorOneReachable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Function.Surjective (buildingLatticeVertexMap P r) := by
  intro q
  apply exists_lattice_of_colorOne_reachable P r q
  cases r with
  | three =>
      exact SphericalHecke.rankThree_colorOneReachable (BaseField P) q
  | four =>
      exact SphericalHecke.rankFour_colorOneReachable (BaseField P) q
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
