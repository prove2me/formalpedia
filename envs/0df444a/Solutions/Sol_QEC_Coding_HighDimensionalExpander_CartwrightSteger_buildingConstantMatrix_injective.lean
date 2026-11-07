-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantMatrix_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:05:03.957587+00:00
-- url     : https://prove2.me/submissions/a5361363-bb14-49c6-ac0d-7ece8142d914

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantRegularMatrix_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingConstantMatrix P r) := by
  intro c d h
  apply constantRegularMatrix_injective P r
  ext i j
  apply (algebraMap (BaseField P) (BuildingLocalField P)).injective
  exact congrFun (congrFun h i) j
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
