-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToIndexLocal_order_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:16:23.829919+00:00
-- url     : https://prove2.me/submissions/5203af13-fa87-48c9-9a23-5eef95847a5f

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneToSplittingSL_order_compatibility

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    cyclicAlgebraNormOneToIndexLocal P r level
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) =
      indexCompletedNormOneInnerFormToIndexLocal P r level
        (orderNormOneInnerFormToCompleted P r level s) := by
  rw [cyclicAlgebraNormOneToIndexLocal, MonoidHom.comp_apply,
    cyclicAlgebraNormOneToSplittingSL_order_compatibility]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change splittingFunctionFieldToIndexCongruenceLocalField P r level
      (constantArithmeticToSplittingFunctionField P r
        ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) i j)) =
    HahnSeries.ofPowerSeries ℤ (ResidueField P r level)
      (indexCompletedArithmeticEval P r level
        ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) i j))
  exact DFunLike.congr_fun
    (splittingFunctionFieldToIndexCongruenceLocalField_constantArithmetic
      P r level)
    ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) i j)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
