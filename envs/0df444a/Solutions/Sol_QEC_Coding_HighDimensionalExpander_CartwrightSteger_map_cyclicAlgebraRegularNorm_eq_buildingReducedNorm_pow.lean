-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_buildingReducedNorm_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:51:13.697721+00:00
-- url     : https://prove2.me/submissions/3e0b9228-a7e4-4bfa-b4f8-e8f49f27fcc4

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicScalarExtension_regularNorm_eq_reducedNorm_pow
import Theorems.Thm_Algebra_norm_tensorProduct_includeRight


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraBuildingReducedNorm P r u :
          (BuildingLocalField P)ˣ) : BuildingLocalField P) ^
        r.matrixRank := by
  calc
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      Algebra.norm (BuildingLocalField P)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := BuildingLocalField P)
          (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) := by
      exact (Algebra.norm_tensorProduct_includeRight
        (functionFieldCyclicBasis P r) (u : CyclicAlgebra P r)).symm
    _ = Algebra.norm (BuildingLocalField P)
        ((cyclicAlgebraUnitToBuildingScalarExtension P r u :
          (BuildingCyclicScalarExtension P r)ˣ) :
            BuildingCyclicScalarExtension P r) := by
      rfl
    _ = _ :=
      buildingCyclicScalarExtension_regularNorm_eq_reducedNorm_pow
        P r (cyclicAlgebraUnitToBuildingScalarExtension P r u)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
