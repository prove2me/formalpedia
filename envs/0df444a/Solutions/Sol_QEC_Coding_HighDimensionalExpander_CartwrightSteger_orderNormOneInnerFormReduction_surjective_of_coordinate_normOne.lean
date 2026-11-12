-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneInnerFormReduction_surjective_of_coordinate_normOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:48:00.841512+00:00
-- url     : https://prove2.me/submissions/5d9d9c00-399d-4cdd-80eb-931d4be05989

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearToPSL_surjective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (hsurj : Function.Surjective
      (orderCyclicMatrixCoordinateNormOneReduction P r level)) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) := by
  intro y
  obtain ⟨s, hs⟩ := specialLinearToPSL_surjective P r level y
  obtain ⟨u, hu⟩ := hsurj s
  refine ⟨orderCyclicMatrixCoordinateNormOneEquiv P r u, ?_⟩
  change specialLinearToPSL P r level
      (orderSpecialLinearReduction P r level
        (orderCyclicMatrixCoordinateNormOneEquiv P r u :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) = y
  rw [← orderCyclicMatrixCoordinateNormOneReduction_apply, hu, hs]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
