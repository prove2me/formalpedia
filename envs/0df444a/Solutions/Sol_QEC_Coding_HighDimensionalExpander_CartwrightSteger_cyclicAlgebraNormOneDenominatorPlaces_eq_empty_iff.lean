-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneDenominatorPlaces_eq_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:52:53.183179+00:00
-- url     : https://prove2.me/submissions/c87d15e2-cdac-4c8f-bc65-d4b10ea65c8d

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmeticFiniteAdeleCyclicIntegralNormOneSet_iff_denominatorPlaces_empty

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    cyclicAlgebraNormOneDenominatorPlaces P r u = ∅ ↔
      cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
        ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r := by
  rw [mem_arithmeticFiniteAdeleCyclicIntegralNormOneSet_iff_denominatorPlaces_empty]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
