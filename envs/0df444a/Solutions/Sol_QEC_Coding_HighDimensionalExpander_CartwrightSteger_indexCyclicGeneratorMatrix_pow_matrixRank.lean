-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorMatrix_pow_matrixRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:04.332819+00:00
-- url     : https://prove2.me/submissions/7bef9c79-3b91-4aed-9ff0-fba85a70604b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftFour_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftThree_pow


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorMatrix P r level ^ r.matrixRank =
      (1 + indexPlaceY P r level) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
  cases r with
  | three => exact shiftThree_pow _ _
  | four => exact shiftFour_pow _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
