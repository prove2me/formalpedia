-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderToCyclicAlgebra_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:46:01.750206+00:00
-- url     : https://prove2.me/submissions/a6ab110f-13c6-48fb-aba5-89f66aeba15b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Function.Injective (cartwrightStegerOrderToCyclicAlgebra P r) := by
  intro x y hxy
  apply Subtype.ext
  calc
    x.1 = (cartwrightStegerOrderToCyclicAlgebra P r x :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) :=
      (cartwrightStegerOrderToCyclicAlgebra_coe P r x).symm
    _ = (cartwrightStegerOrderToCyclicAlgebra P r y :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) :=
      congrArg (fun z : CyclicAlgebra P r => z.1) hxy
    _ = y.1 := cartwrightStegerOrderToCyclicAlgebra_coe P r y
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
