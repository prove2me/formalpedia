-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:02:11.658673+00:00
-- url     : https://prove2.me/submissions/72243b79-091f-43da-a3c3-c8a90ac2d321

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
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
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    globalIntegralUnitPGLHom P r (skewLaurentMonomialUnit P r c n) =
      globalConstantPGLHom P r c *
        globalCyclicGeneratorPGL P r ^ n := by
  apply congrArg (Matrix.ProjGenLinGroup.mk :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank)
        (SplittingFunctionField P r))
  apply Units.ext
  change skewLaurentToGlobalMatrix P r
      (SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
        (c : ConstantExtension P r)) = _
  rw [skewLaurentToGlobalMatrix_single]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
