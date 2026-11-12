-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_cyclicAlgebraNormOne_with_finite_offTarget_denominators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:56:03.617628+00:00
-- url     : https://prove2.me/submissions/758ead70-8359-4e4e-850b-ff4ce24b4b34

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneDenominatorPlaces_finite
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    ∃ u : CyclicAlgebraNormOne P r,
      cyclicAlgebraNormOneToIndexLocal P r level u ∈
          indexLocalNormOneFiniteTargetNeighborhood P r level g ∧
        (cyclicAlgebraNormOneDenominatorPlaces P r u).Finite ∧
        indexCongruencePlace P r level ∉
          cyclicAlgebraNormOneDenominatorPlaces P r u := by
  obtain ⟨u, hu⟩ :=
    exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
      P r level g
  exact ⟨u, hu,
    cyclicAlgebraNormOneDenominatorPlaces_finite P r u,
    indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces
      P r level g u hu⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
