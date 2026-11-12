-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOne_reduction_compatible_with_full_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:48:27.029965+00:00
-- url     : https://prove2.me/submissions/74b440b0-000e-465f-8d34-e44dcc7b12bd

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
      orderInnerFormNormOneReductionToPGL P r level
        (orderNormOneInnerFormEquivFullNormOne P r s) := by
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
