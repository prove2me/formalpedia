-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_cyclicAlgebraNormOneToIndexLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:24:02.91219+00:00
-- url     : https://prove2.me/submissions/fea48866-8bf7-47ed-9ba6-8c70bb38d034

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_denseRange_cyclicAlgebraUnitToIndexLocalGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_continuous_indexLocalGLCommutatorToSL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraUnitCommutatorNormOne_compatibility
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinearGroup_commutator_eq_top


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (cyclicAlgebraNormOneToIndexLocal P r level) := by
  let f : (CyclicAlgebra P r)ˣ →
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level) :=
    Units.map
      (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom
  let c :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) ×
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (IndexCongruenceLocalField P r level) →
      IndexLocalNormOneInnerForm P r level :=
    fun p => indexLocalGLCommutatorToSL P r level p.1 p.2
  let H : Subgroup (IndexLocalNormOneInnerForm P r level) :=
    (cyclicAlgebraNormOneToIndexLocal P r level).range.topologicalClosure
  have hf : DenseRange f :=
    denseRange_cyclicAlgebraUnitToIndexLocalGL P r level
  have hpair : DenseRange (Prod.map f f) := hf.prodMap hf
  have hc : Continuous c :=
    continuous_indexLocalGLCommutatorToSL P r level
  have himage : c '' Set.range (Prod.map f f) ⊆
      Set.range (cyclicAlgebraNormOneToIndexLocal P r level) := by
    rintro z ⟨p, ⟨q, rfl⟩, rfl⟩
    rcases q with ⟨u, v⟩
    refine ⟨cyclicAlgebraUnitCommutatorNormOne P r u v, ?_⟩
    exact cyclicAlgebraUnitCommutatorNormOne_compatibility P r level u v
  have hcomm : ∀ a b :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level),
      indexLocalGLCommutatorToSL P r level a b ∈ H := by
    intro a b
    change c (a, b) ∈ H
    change c (a, b) ∈ closure
      (Set.range (cyclicAlgebraNormOneToIndexLocal P r level))
    exact closure_mono himage
      (hc.range_subset_closure_image_dense hpair (Set.mem_range_self (a, b)))
  have hcommutator :
      commutator (IndexLocalNormOneInnerForm P r level) ≤ H := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact hcomm (Matrix.SpecialLinearGroup.toGL a)
      (Matrix.SpecialLinearGroup.toGL b)
  rw [specialLinearGroup_commutator_eq_top r] at hcommutator
  have hHtop : H = ⊤ := top_unique hcommutator
  rw [DenseRange, dense_iff_closure_eq]
  change (H : Set (IndexLocalNormOneInnerForm P r level)) = Set.univ
  rw [hHtop]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
