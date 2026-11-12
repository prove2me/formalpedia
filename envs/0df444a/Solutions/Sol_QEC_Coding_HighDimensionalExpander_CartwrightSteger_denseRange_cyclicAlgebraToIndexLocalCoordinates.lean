-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_cyclicAlgebraToIndexLocalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:09:48.017309+00:00
-- url     : https://prove2.me/submissions/b8237458-1164-415a-955e-8cb961114d4b

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
    DenseRange (cyclicAlgebraToIndexLocalCoordinates P r level) := by
  let f : ((Fin r.matrixRank × Fin r.matrixRank) → FunctionField P) →
      ((Fin r.matrixRank × Fin r.matrixRank) →
        IndexCongruenceLocalField P r level) :=
    Pi.map fun _ => functionFieldToIndexCongruenceLocalField P r level
  have hf : DenseRange f :=
    DenseRange.piMap fun _ =>
      denseRange_functionFieldToIndexCongruenceLocalField P r level
  have hsurj : Function.Surjective
      (functionFieldCyclicBasis P r).equivFun :=
    (functionFieldCyclicBasis P r).equivFun.surjective
  rw [show cyclicAlgebraToIndexLocalCoordinates P r level =
      f ∘ (functionFieldCyclicBasis P r).equivFun by rfl,
    DenseRange, Set.range_comp, hsurj.range_eq, Set.image_univ]
  exact hf
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
