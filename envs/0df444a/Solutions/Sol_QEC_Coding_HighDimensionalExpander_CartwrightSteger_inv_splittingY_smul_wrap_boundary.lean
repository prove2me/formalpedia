-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.inv_splittingY_smul_wrap_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:20:26.347563+00:00
-- url     : https://prove2.me/submissions/dfdf2c07-a0d6-4fc3-ab38-c24160eaf2ca

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_onePlusY_eq_one_add_splittingY


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (S D : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    -D + (splittingY P r)⁻¹ •
        (S + (onePlusY P r) • D - D) =
      (splittingY P r)⁻¹ • S := by
  rw [smul_sub, smul_add, smul_smul]
  have hscalar :
      (splittingY P r)⁻¹ * onePlusY P r =
        (splittingY P r)⁻¹ + 1 := by
    rw [onePlusY_eq_one_add_splittingY]
    field_simp [splittingY_ne_zero]
  rw [hscalar, add_smul, one_smul]
  abel
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
