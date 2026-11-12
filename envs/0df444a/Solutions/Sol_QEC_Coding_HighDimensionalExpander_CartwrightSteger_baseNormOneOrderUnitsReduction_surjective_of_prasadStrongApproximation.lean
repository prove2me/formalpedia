-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseNormOneOrderUnitsReduction_surjective_of_prasadStrongApproximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:57:02.328446+00:00
-- url     : https://prove2.me/submissions/b005acde-d283-4295-902e-e148f03b5b34

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
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r)) :
    Function.Surjective (baseNormOneOrderUnitsReduction P r level) := by
  rw [← sIntegralNormOneReductionToPSL_eq_baseReduction P r level]
  exact
    sIntegralNormOneReductionToPSL_surjective_of_prasadStrongApproximation
      P r level hPrasad
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
