-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:53:36.710404+00:00
-- url     : https://prove2.me/submissions/bfb23530-b546-4107-9119-02802bd073b4

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingFrobeniusMatrix_mul_buildingConstantMatrix

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingCyclicGeneratorMatrix P r * buildingConstantMatrix P r c =
      buildingConstantMatrix P r (constantFrobenius P r c) *
        buildingCyclicGeneratorMatrix P r := by
  rw [buildingCyclicGeneratorMatrix, Matrix.smul_mul, Matrix.mul_smul,
    buildingFrobeniusMatrix_mul_buildingConstantMatrix]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
