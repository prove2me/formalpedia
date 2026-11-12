-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_cyclicAlgebraUnitToIndexLocalGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:17:35.423201+00:00
-- url     : https://prove2.me/submissions/c252c0ed-c27d-4aed-b1ab-56f396f25e12

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_cyclicAlgebraToIndexLocalMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isOpenEmbedding_indexLocalMatrix_unitsVal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange
      (Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom) := by
  letI : DivisionRing (CyclicAlgebra P r) := cyclicAlgebraDivisionRing P r
  rw [DenseRange]
  apply dense_iff_inter_open.mpr
  intro U hUopen hUne
  let V : Set (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) := Units.val '' U
  have hVopen : IsOpen V :=
    (isOpenEmbedding_indexLocalMatrix_unitsVal P r level).isOpenMap U hUopen
  have hVne : V.Nonempty := hUne.image Units.val
  obtain ⟨M, hMV, hMrange⟩ := dense_iff_inter_open.mp
    (denseRange_cyclicAlgebraToIndexLocalMatrix P r level) V hVopen hVne
  obtain ⟨x, rfl⟩ := hMrange
  obtain ⟨g, hgU, hg⟩ := hMV
  have hx : x ≠ 0 := by
    intro hx0
    subst x
    have hg0 : (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) = 0 := by
      exact hg.trans (map_zero (cyclicAlgebraToIndexLocalMatrix P r level))
    exact g.isUnit.ne_zero hg0
  let xUnit : (CyclicAlgebra P r)ˣ := Units.mk0 x hx
  refine ⟨Units.map
      (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom xUnit,
    ?_, Set.mem_range_self xUnit⟩
  have hunitEq : Units.map
      (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom xUnit = g := by
    apply Units.ext
    exact hg.symm
  rwa [hunitEq]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
