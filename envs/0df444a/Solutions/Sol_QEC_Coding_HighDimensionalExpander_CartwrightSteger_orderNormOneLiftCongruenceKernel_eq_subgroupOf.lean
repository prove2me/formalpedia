-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderNormOneLiftCongruenceKernel_eq_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:49:54.115507+00:00
-- url     : https://prove2.me/submissions/2c93be9f-0f7b-4369-9549-ed8e6690b1e9

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
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneLiftCongruenceKernel P r level =
      (OrderNormOneCongruenceSubgroup P r level).subgroupOf
        (OrderNormOneLiftCongruenceProduct P r level) := by
  ext g
  change orderNormOneLiftCongruenceReduction P r level g = 1 ↔
    (g : OrderNormOneInnerForm P r) ∈
      OrderNormOneCongruenceSubgroup P r level
  constructor
  · intro hg
    have hg' : orderNormOneInnerFormReduction P r level
        (g : OrderNormOneInnerForm P r) = 1 :=
      congrArg Subtype.val hg
    rw [orderNormOneCongruenceSubgroup_eq_reduction_ker]
    exact hg'
  · intro hg
    apply Subtype.ext
    rw [orderNormOneCongruenceSubgroup_eq_reduction_ker] at hg
    exact hg
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
