-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.finrank_cyclicAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:48:09.491261+00:00
-- url     : https://prove2.me/submissions/b4a3aeeb-c291-416d-b9e3-046bd6f76c5c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Module.finrank (FunctionField P) (CyclicAlgebra P r) =
      r.matrixRank * r.matrixRank := by
  rw [Module.finrank_eq_card_basis (functionFieldCyclicBasis P r),
    Fintype.card_prod, Fintype.card_fin]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
