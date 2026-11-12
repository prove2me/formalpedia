-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_generatorRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:37:12.188307+00:00
-- url     : https://prove2.me/submissions/879127c9-173e-4f34-902a-7d9270b610e6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : ConstantProjectiveClass P r) :
    ((orderNormOneInnerFormReduction P r level
        (orderNormOneGeneratorRatio P r u v) : PSL P r level) :
      PGL P r level) =
      indexCartwrightStegerClassGenerator P r level u *
        (indexCartwrightStegerClassGenerator P r level v)⁻¹ := by
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL
        (orderSpecialLinearReduction P r level
          (orderSplitGeneratorRatioSpecial P r u v))) = _
  have hmap : Matrix.SpecialLinearGroup.toGL
      (orderSpecialLinearReduction P r level
        (orderSplitGeneratorRatioSpecial P r u v)) =
      Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (Matrix.SpecialLinearGroup.toGL
          (orderSplitGeneratorRatioSpecial P r u v)) := by
    apply Units.ext
    rfl
  have hto : Matrix.SpecialLinearGroup.toGL
        (orderSplitGeneratorRatioSpecial P r u v) =
      orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹ := by
    apply Units.ext
    rfl
  rw [hmap, hto]
  change orderSplitReductionPGLHom P r level
      (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹) = _
  rw [map_mul, map_inv,
    orderSplitReductionPGLHom_classGenerator,
    orderSplitReductionPGLHom_classGenerator]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
