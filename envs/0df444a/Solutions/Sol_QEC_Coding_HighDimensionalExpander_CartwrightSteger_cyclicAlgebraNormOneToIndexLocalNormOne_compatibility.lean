-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToIndexLocalNormOne_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:46:43.479812+00:00
-- url     : https://prove2.me/submissions/87c3105d-56e7-4450-ac2a-5f30d7bc0fab

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
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CyclicAlgebraNormOne P r) :
    indexLocalCyclicAlgebraNormOneEquivSL P r level
        (cyclicAlgebraNormOneToIndexLocalNormOne P r level u) =
      cyclicAlgebraNormOneToIndexLocal P r level u := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hleft : Matrix.SpecialLinearGroup.toGL
      (indexLocalCyclicAlgebraNormOneEquivSL P r level
        (cyclicAlgebraNormOneToIndexLocalNormOne P r level u)) =
      indexLocalCyclicAlgebraUnitEquivGL P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level u) := by
    apply Units.ext
    rfl
  have hright : Matrix.SpecialLinearGroup.toGL
      (cyclicAlgebraNormOneToIndexLocal P r level u) =
      Matrix.GeneralLinearGroup.map
        (splittingFunctionFieldToIndexCongruenceLocalField P r level)
          (Matrix.SpecialLinearGroup.toGL
            (cyclicAlgebraNormOneToSplittingSL P r u)) := by
    apply Units.ext
    rfl
  rw [hleft, hright]
  rw [indexLocalCyclicAlgebraUnitEquivGL_global_compatibility,
    cyclicAlgebraNormOneToSplittingSL_toGL]
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
