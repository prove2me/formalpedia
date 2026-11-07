-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_eq_constant_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:37:28.241296+00:00
-- url     : https://prove2.me/submissions/99990cd8-3a39-4da2-bd65-7fec7e2c738c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_zpow_of_skewLaurent_unit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerSkewLaurentRing P r)ˣ) :
    ∃ c : (ConstantExtension P r)ˣ, ∃ n : ℤ,
      globalIntegralUnitPGLHom P r u =
        globalConstantPGLHom P r c *
          globalCyclicGeneratorPGL P r ^ n := by
  obtain ⟨c, n, hu⟩ := exists_constant_zpow_of_skewLaurent_unit P r u
  refine ⟨c, n, ?_⟩
  have hmatrix := congrArg (skewLaurentToGlobalMatrix P r) hu
  rw [skewLaurentToGlobalMatrix_single] at hmatrix
  have hGL : globalIntegralUnitGLHom P r u =
      Units.map (constantMatrixEmbedding P r).toMonoidHom c *
        cyclicGenerator P r ^ n := by
    apply Units.ext
    exact hmatrix
  exact congrArg (Matrix.ProjGenLinGroup.mk :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) hGL
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
