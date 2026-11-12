-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruenceLocalRingToCompletion_indexPlacePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:09:16.485915+00:00
-- url     : https://prove2.me/submissions/1dc59a29-14be-4155-9f8e-e0ce82b900af

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
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCongruenceLocalRingToCompletion P r level
        (algebraMap (ArithmeticRing P)
          (IndexCongruenceLocalRing P r level)
          (algebraMap (PolynomialRing P) (ArithmeticRing P)
            (indexPlacePolynomial P r level))) =
      indexCompletedUniformizer P r level := by
  rw [indexCongruenceLocalRingToCompletion_algebraMap,
    indexCompletedBaseArithmeticEval_algebraMap,
    indexCompletedBasePolynomialEval_indexPlacePolynomial]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
