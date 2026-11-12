-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_indexCompletedBaseArithmeticEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:11:36.020436+00:00
-- url     : https://prove2.me/submissions/57b6e5da-6d8c-4583-8850-6efba6572714

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
    DenseRange (indexCompletedBaseArithmeticEval P r level) := by
  intro s
  choose a ha using fun n =>
    exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
      P r level s n
  apply mem_closure_of_tendsto
    (f := fun n : Nat => indexCompletedBaseArithmeticEval P r level (a n))
    (b := (Filter.atTop : Filter Nat))
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) =>
      ha n k hkn
  · exact Filter.Eventually.of_forall fun n => Set.mem_range_self (a n)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
