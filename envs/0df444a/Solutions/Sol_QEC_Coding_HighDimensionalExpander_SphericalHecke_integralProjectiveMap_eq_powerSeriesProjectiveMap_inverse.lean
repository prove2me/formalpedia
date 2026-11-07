-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:26:09.740198+00:00
-- url     : https://prove2.me/submissions/6e68037b-4aa8-4ebe-aa8f-763ad989e9e8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinearToInteger_inverse
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeries_integer_local_triangle


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    integralProjectiveMap k d g =
      powerSeriesProjectiveMap k d
        (integerGeneralLinearToPowerSeries k d g) := by
  change Matrix.ProjGenLinGroup.mk (integralGeneralLinearToLocal k d g) =
    Matrix.ProjGenLinGroup.mk (powerSeriesGeneralLinearToLocal k d
      (integerGeneralLinearToPowerSeries k d g))
  congr 1
  rw [← powerSeries_integer_local_triangle,
    powerSeriesGeneralLinearToInteger_inverse]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
