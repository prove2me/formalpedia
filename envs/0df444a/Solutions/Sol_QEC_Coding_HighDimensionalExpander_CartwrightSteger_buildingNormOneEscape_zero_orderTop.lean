-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingNormOneEscape_zero_orderTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:07:00.798352+00:00
-- url     : https://prove2.me/submissions/52756095-e3c7-43d8-a809-247d421865d4

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
    (P : BasePrime) (r : Rank) (n : Nat) :
    (((buildingNormOneEscape P r n :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (buildingEscapeIndexZero r) (buildingEscapeIndexZero r)).orderTop =
      (n : WithTop Int) := by
  rw [buildingNormOneEscape_apply_zero_zero]
  exact SphericalHecke.orderTop_uniformizerUnit_pow n
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
