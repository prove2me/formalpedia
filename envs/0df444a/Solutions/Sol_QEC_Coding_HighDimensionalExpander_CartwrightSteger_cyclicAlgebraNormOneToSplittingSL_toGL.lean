-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToSplittingSL_toGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:36:50.250551+00:00
-- url     : https://prove2.me/submissions/073fadae-f420-45de-9a6d-d5d31705d96c

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

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    Matrix.SpecialLinearGroup.toGL
        (cyclicAlgebraNormOneToSplittingSL P r u) =
      cyclicAlgebraUnitToGlobalGL P r u := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change ((splittingCyclicScalarExtensionUnitEquivGL P r
      (cyclicAlgebraUnitToSplittingScalarExtension P r u) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) i j = _
  exact congrArg (fun M : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r) =>
    ((M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) i j))
    (splittingScalarExtensionUnitEquivGL_global_compatibility P r u)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
