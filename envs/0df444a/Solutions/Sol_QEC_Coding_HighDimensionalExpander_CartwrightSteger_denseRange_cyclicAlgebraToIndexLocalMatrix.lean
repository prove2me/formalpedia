-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_cyclicAlgebraToIndexLocalMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:13:41.70189+00:00
-- url     : https://prove2.me/submissions/825b23ff-146a-43aa-b093-9a4bbc46d9ae

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_continuous_indexLocalCyclicBasis_equivFun_symm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_cyclicAlgebraToIndexLocalCoordinates

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
    DenseRange (cyclicAlgebraToIndexLocalMatrix P r level) := by
  let assemble := (indexLocalCyclicBasis P r level).equivFun.symm
  have hassemble : DenseRange assemble :=
    assemble.surjective.denseRange
  have hcomp : DenseRange
      (assemble ∘ cyclicAlgebraToIndexLocalCoordinates P r level) :=
    hassemble.comp
      (denseRange_cyclicAlgebraToIndexLocalCoordinates P r level)
      (continuous_indexLocalCyclicBasis_equivFun_symm P r level)
  have heq : assemble ∘ cyclicAlgebraToIndexLocalCoordinates P r level =
      cyclicAlgebraToIndexLocalMatrix P r level := by
    funext x
    change assemble (cyclicAlgebraToIndexLocalCoordinates P r level x) = _
    rw [show assemble (cyclicAlgebraToIndexLocalCoordinates P r level x) =
        ∑ p, functionFieldToIndexCongruenceLocalField P r level
            ((functionFieldCyclicBasis P r).equivFun x p) •
          indexLocalCyclicBasis P r level p by
      exact Module.Basis.equivFun_symm_apply
        (indexLocalCyclicBasis P r level)
        (cyclicAlgebraToIndexLocalCoordinates P r level x)]
    conv_rhs =>
      rw [← (functionFieldCyclicBasis P r).sum_equivFun x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, cyclicAlgebraToIndexLocalMatrix_basis,
      indexLocalCyclicBasis_apply]
    change functionFieldToIndexCongruenceLocalField P r level
        ((functionFieldCyclicBasis P r).equivFun x p) •
          indexLocalCyclicBasisVector P r level p =
      functionFieldToIndexCongruenceLocalField P r level
        ((functionFieldCyclicBasis P r).equivFun x p) •
          indexLocalCyclicBasisVector P r level p
    rfl
  rw [← heq]
  exact hcomp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
