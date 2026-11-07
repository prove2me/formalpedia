-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:21:30.126974+00:00
-- url     : https://prove2.me/submissions/b83a6a78-c698-49e2-8f57-96adf872a3ac

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c d : ConstantExtension P r) :
    buildingConstantMatrix P r c * buildingConstantMatrix P r d =
      buildingConstantMatrix P r (c * d) := by
  change (constantRegularMatrix P r c).map
      (algebraMap (BaseField P) (BuildingLocalField P)) *
    (constantRegularMatrix P r d).map
      (algebraMap (BaseField P) (BuildingLocalField P)) = _
  rw [← Matrix.map_mul, ← map_mul]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
