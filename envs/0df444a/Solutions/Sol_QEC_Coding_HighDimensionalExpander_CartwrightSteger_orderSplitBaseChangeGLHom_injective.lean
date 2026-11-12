-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderSplitBaseChangeGLHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:45:14.635243+00:00
-- url     : https://prove2.me/submissions/2e6add8c-fc9b-4a2b-b537-13328d3696ac

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
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderSplitBaseChangeGLHom P r) := by
  intro A B hAB
  apply Units.ext
  ext i j
  apply constantArithmeticToSplittingFunctionField_injective P r
  exact congrArg (fun M : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (SplittingFunctionField P r) =>
    ((M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) i j)) hAB
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
