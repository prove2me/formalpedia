-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitToIndexPlace_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:53:22.223286+00:00
-- url     : https://prove2.me/submissions/aa8982e4-fe95-4eec-8e0e-7b542eacaf1c

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
    Function.Surjective
      (arithmeticFiniteAdeleCyclicUnitToIndexPlace P r level) := by
  intro u
  exact ⟨arithmeticFiniteAdeleCyclicUnitSupportedAtIndexPlace P r level u,
    arithmeticFiniteAdeleCyclicUnitToIndexPlace_supported P r level u⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
