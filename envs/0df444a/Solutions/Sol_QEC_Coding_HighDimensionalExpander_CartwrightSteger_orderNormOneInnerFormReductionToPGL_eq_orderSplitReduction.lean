-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:18:12.738578+00:00
-- url     : https://prove2.me/submissions/913300e2-723b-4f9e-9ec6-9b84017a68a4

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
    (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormReductionToPGL P r level s =
      orderSplitReductionPGLHom P r level
        (orderNormOneInnerFormToSplitGL P r s) := by
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL
        (orderSpecialLinearReduction P r level
          (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)))) =
    orderSplitReductionPGLHom P r level
      (Matrix.SpecialLinearGroup.toGL
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)))
  have hmap : Matrix.SpecialLinearGroup.toGL
      (orderSpecialLinearReduction P r level
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))) =
      Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (Matrix.SpecialLinearGroup.toGL
          (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) := by
    apply Units.ext
    rfl
  rw [hmap]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
