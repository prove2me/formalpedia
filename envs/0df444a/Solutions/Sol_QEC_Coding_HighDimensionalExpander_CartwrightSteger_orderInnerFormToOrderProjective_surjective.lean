-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderInnerFormToOrderProjective_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:47:47.713566+00:00
-- url     : https://prove2.me/submissions/a469274d-651d-41d7-98e7-4fd97e610fbc

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderSplitCompactNormalFormGL_mem_innerForm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderProjectivization_eq_of_globalPGL_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderInnerFormToOrderProjective P r) := by
  intro q
  let u : (CartwrightStegerOrder P r)ˣ := q.out
  obtain ⟨x, hx, c, j, hglobal⟩ :=
    exists_orderSplitCartwrightSteger_mul_compact_of_orderUnit P r u
  let gGL : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
    x * orderSplitCompactNormalFormGL P r c j
  have hgInner : gGL ∈ OrderInnerFormUnits P r :=
    (OrderInnerFormUnits P r).mul_mem
      (OrderSplitCartwrightStegerLattice_le_innerForm P r hx)
      (orderSplitCompactNormalFormGL_mem_innerForm P r c j)
  let g : OrderInnerFormUnits P r := ⟨gGL, hgInner⟩
  refine ⟨g, ?_⟩
  change cartwrightStegerOrderProjectivization P r
      (orderInnerFormToOrderUnits P r g) = q
  calc
    cartwrightStegerOrderProjectivization P r
        (orderInnerFormToOrderUnits P r g) =
      cartwrightStegerOrderProjectivization P r u := by
        apply cartwrightStegerOrderProjectivization_eq_of_globalPGL_eq
        rw [orderUnitToGlobalPGL]
        change Matrix.ProjGenLinGroup.mk
            (orderUnitToGlobalGL P r
              (orderInnerFormToOrderUnits P r g)) = _
        rw [orderUnitToGlobalGL_orderInnerFormToOrderUnits]
        exact hglobal.symm
    _ = q := QuotientGroup.out_eq' q
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
