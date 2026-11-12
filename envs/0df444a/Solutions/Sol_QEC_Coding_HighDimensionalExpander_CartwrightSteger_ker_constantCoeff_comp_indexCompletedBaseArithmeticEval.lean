-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ker_constantCoeff_comp_indexCompletedBaseArithmeticEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:53:39.957345+00:00
-- url     : https://prove2.me/submissions/845709b8-2cdc-466e-9a4f-3876c0c25ce2

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
    RingHom.ker
        (PowerSeries.constantCoeff.comp
          (indexCompletedBaseArithmeticEval P r level)) =
      IndexCongruenceIdeal P r level := by
  ext a
  change PowerSeries.constantCoeff
      (indexCompletedBaseArithmeticEval P r level a) = 0 ↔
    indexArithmeticEval P r level a = 0
  rw [indexCompletedBaseArithmeticEval_constantCoeff]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
