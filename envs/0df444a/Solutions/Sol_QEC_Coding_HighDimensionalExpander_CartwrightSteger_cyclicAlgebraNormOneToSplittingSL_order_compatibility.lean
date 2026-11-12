-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToSplittingSL_order_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:11:50.511973+00:00
-- url     : https://prove2.me/submissions/1893ab61-c969-4e70-b7ec-81e48e284710

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneToSplittingSL_toGL

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    cyclicAlgebraNormOneToSplittingSL P r
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) =
      Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        (constantArithmeticToSplittingFunctionField P r)
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [cyclicAlgebraNormOneToSplittingSL_toGL]
  change orderUnitToGlobalGL P r
      (orderNormOneInnerFormToOrderUnits P r s) = _
  rw [orderUnitToGlobalGL_orderNormOneInnerFormToOrderUnits]
  apply Units.ext
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
