-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingFrobeniusMatrix_mul_buildingConstantMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:44.479995+00:00
-- url     : https://prove2.me/submissions/5210a107-a5bc-456f-a6f0-92ffd1e58e50

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_mul_constantRegularMatrix


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    buildingFrobeniusMatrix P r * buildingConstantMatrix P r c =
      buildingConstantMatrix P r (constantFrobenius P r c) *
        buildingFrobeniusMatrix P r := by
  change
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).map
          (algebraMap (BaseField P) (BuildingLocalField P)) *
      (constantRegularMatrix P r c).map
          (algebraMap (BaseField P) (BuildingLocalField P)) =
    (constantRegularMatrix P r (constantFrobenius P r c)).map
          (algebraMap (BaseField P) (BuildingLocalField P)) *
      (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)).map
          (algebraMap (BaseField P) (BuildingLocalField P))
  rw [← Matrix.map_mul, frobeniusGL_mul_constantRegularMatrix,
    Matrix.map_mul]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
