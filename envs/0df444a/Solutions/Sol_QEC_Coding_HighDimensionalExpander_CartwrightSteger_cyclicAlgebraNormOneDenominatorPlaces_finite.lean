-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneDenominatorPlaces_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:16:03.948614+00:00
-- url     : https://prove2.me/submissions/14ba0692-6f6e-4bde-b9d7-e9cae5bb0c08

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_finite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : CyclicAlgebraNormOne P r) :
    (cyclicAlgebraNormOneDenominatorPlaces P r u).Finite :=
  arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_finite P r
    (cyclicAlgebraUnitToArithmeticFiniteAdeles P r u)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
