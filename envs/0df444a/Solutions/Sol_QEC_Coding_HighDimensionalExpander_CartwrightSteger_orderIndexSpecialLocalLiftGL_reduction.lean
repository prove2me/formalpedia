-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexSpecialLocalLiftGL_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:44:16.031434+00:00
-- url     : https://prove2.me/submissions/ed7113f6-784b-464e-9af7-4fd585f597fa

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexMatrixLocalLift_reduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.GeneralLinearGroup.map (indexLocalReduction P r level)
        (orderIndexSpecialLocalLiftGL P r level s) =
      Matrix.SpecialLinearGroup.toGL s := by
  apply Units.ext
  change (orderIndexSpecialLocalLiftGL P r level s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexLocalCoefficientRing P r level)).map
          (indexLocalReduction P r level) =
    (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level))
  rw [orderIndexSpecialLocalLiftGL_coe]
  exact orderIndexMatrixLocalLift_reduction P r level s
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
