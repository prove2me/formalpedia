-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:59:20.464198+00:00
-- url     : https://prove2.me/submissions/1cc7ea02-519f-4d23-9e9f-c92b1b7660dc

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantUnitMatrix P r u)⁻¹ = constantUnitMatrix P r u⁻¹ := by
  change (constantUnitMatrixHom P r u)⁻¹ = constantUnitMatrixHom P r u⁻¹
  rw [map_inv]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
