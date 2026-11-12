-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleAtIndexLocalField_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:55:14.223195+00:00
-- url     : https://prove2.me/submissions/0824dfb1-7b19-4ac3-a827-fb2073a91a04

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
open scoped PowerSeries.WithPiTopology Topology WithZeroTopology Multiplicative
open MonoidWithZeroHom.ValueGroup₀
open Filter
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.selectedPlaceResidueFieldTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.selectedPlaceResidueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (arithmeticFiniteAdeleAtIndexLocalField P r level) := by
  intro x
  exact ⟨arithmeticFiniteAdeleSupportedAtIndexLocalField P r level x,
    arithmeticFiniteAdeleAtIndexLocalField_supported P r level x⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
