-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.inv_splittingY_smul_add_splittingY_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:20:27.492197+00:00
-- url     : https://prove2.me/submissions/af185e9c-c617-4539-8ff6-414819f44fab

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (F K : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    (splittingY P r)⁻¹ • (F + (splittingY P r) • K) =
      K + (splittingY P r)⁻¹ • F := by
  rw [smul_add, smul_smul]
  rw [inv_mul_cancel₀ (splittingY_ne_zero P r), one_smul]
  abel
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
