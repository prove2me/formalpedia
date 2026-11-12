-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_cyclicAlgebraNormOne_mem_indexLocalFiniteTargetNeighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:27:47.841476+00:00
-- url     : https://prove2.me/submissions/f1433308-d7bd-4b85-922c-5b72b27ff357

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_cyclicAlgebraNormOneToIndexLocal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isOpen_indexLocalNormOneFiniteTargetNeighborhood
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_finiteSpecialLinearToIndexLocalNormOne_mem_neighborhood

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
        indexLocalNormOneFiniteTargetNeighborhood P r level g := by
  let U := indexLocalNormOneFiniteTargetNeighborhood P r level g
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := dense_iff_inter_open.mp
    (denseRange_cyclicAlgebraNormOneToIndexLocal P r level) U
    (isOpen_indexLocalNormOneFiniteTargetNeighborhood P r level g)
    ⟨finiteSpecialLinearToIndexLocalNormOne P r level g,
      finiteSpecialLinearToIndexLocalNormOne_mem_neighborhood P r level g⟩
  exact ⟨u, hu⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
