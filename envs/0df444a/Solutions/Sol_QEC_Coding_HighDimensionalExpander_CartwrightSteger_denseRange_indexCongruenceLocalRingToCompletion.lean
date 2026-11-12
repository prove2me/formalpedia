-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_indexCongruenceLocalRingToCompletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:55:39.804207+00:00
-- url     : https://prove2.me/submissions/b97f5401-3f15-4c47-bbf9-4acde75dd1c1

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_indexCompletedBaseArithmeticEval

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
    DenseRange (indexCongruenceLocalRingToCompletion P r level) := by
  apply (denseRange_indexCompletedBaseArithmeticEval P r level).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨algebraMap (ArithmeticRing P)
      (IndexCongruenceLocalRing P r level) a,
    indexCongruenceLocalRingToCompletion_algebraMap P r level a⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
