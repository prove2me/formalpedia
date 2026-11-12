-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicUnitToBuildingGL_orderYUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:43:26.904211+00:00
-- url     : https://prove2.me/submissions/11628024-d2f9-4693-b262-8ff254f4a521

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (cartwrightStegerOrderYUnit P r)) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (buildingLocalYUnit P) := by
  apply Units.ext
  change cyclicAlgebraToBuilding P r
      ((orderUnitToCyclicUnit P r (cartwrightStegerOrderYUnit P r) :
        (CyclicAlgebra P r)ˣ) : CyclicAlgebra P r) =
    Matrix.scalar (Fin r.matrixRank) (buildingLocalY P)
  have hsource : ((orderUnitToCyclicUnit P r
        (cartwrightStegerOrderYUnit P r) : (CyclicAlgebra P r)ˣ) :
      CyclicAlgebra P r) =
      algebraMap (FunctionField P) (CyclicAlgebra P r) RatFunc.X := by
    apply Subtype.ext
    change Matrix.scalar (Fin r.matrixRank) (splittingY P r) =
      Matrix.scalar (Fin r.matrixRank)
        (functionFieldEmbedding P r RatFunc.X)
    rw [functionFieldEmbedding_X, splittingY]
  rw [hsource]
  calc
    _ = algebraMap (FunctionField P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        RatFunc.X := (cyclicAlgebraToBuilding P r).commutes RatFunc.X
    _ = Matrix.scalar (Fin r.matrixRank)
        (functionFieldToBuildingLocalField P RatFunc.X) := rfl
    _ = _ := congrArg (Matrix.scalar (Fin r.matrixRank))
      (functionFieldToBuildingLocalField_X P)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
