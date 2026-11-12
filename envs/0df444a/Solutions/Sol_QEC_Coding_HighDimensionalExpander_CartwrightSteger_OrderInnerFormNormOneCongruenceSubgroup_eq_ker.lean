-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.OrderInnerFormNormOneCongruenceSubgroup_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:19:30.925624+00:00
-- url     : https://prove2.me/submissions/91e9ffee-a5bd-4007-8b55-207b55b4affb

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_OrderInnerFormCongruenceSubgroup_eq_reduction_ker

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormNormOneCongruenceSubgroup P r level =
      (orderInnerFormNormOneReduction P r level).ker := by
  ext g
  change (g : OrderInnerFormUnits P r) ∈
      OrderInnerFormCongruenceSubgroup P r level ↔
    orderInnerFormNormOneReduction P r level g = 1
  rw [OrderInnerFormCongruenceSubgroup_eq_reduction_ker]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
