-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.map_coordinateGrassmannian_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:24:59.126723+00:00
-- url     : https://prove2.me/submissions/6a143720-c749-4526-a5c9-c35d7a95f3c3

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_mem_coordinateGrassmannian_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) k) :
    (coordinateGrassmannian k d r hr).1.map
        (Matrix.GeneralLinearGroup.toLin g).val =
        (coordinateGrassmannian k d r hr).1 ↔
      ∀ i j : Fin d, r ≤ i.val → j.val < r → g i j = 0 := by
  let P := (coordinateGrassmannian k d r hr).1
  let e := Matrix.GeneralLinearGroup.toLin g
  constructor
  · intro hmap i j hi hj
    let j' : Fin r := ⟨j.val, hj⟩
    have hj_eq : Fin.castLE hr j' = j := by apply Fin.ext; rfl
    have hframe : coordinateFrame k d r hr j' ∈ P := by
      exact Submodule.subset_span ⟨j', rfl⟩
    change P.map e.val = P at hmap
    have himage : e.val (coordinateFrame k d r hr j') ∈ P.map e.val :=
      ⟨coordinateFrame k d r hr j', hframe, rfl⟩
    rw [hmap] at himage
    have hzero := (mem_coordinateGrassmannian_iff k d r hr _).mp himage i hi
    change Matrix.mulVec (g : Matrix (Fin d) (Fin d) k)
      (coordinateFrame k d r hr j') i = 0 at hzero
    simpa [coordinateFrame, Matrix.mulVec_single_one, hj_eq] using hzero
  · intro hblock
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      apply (mem_coordinateGrassmannian_iff k d r hr _).mpr
      intro i hi
      have hxzero := (mem_coordinateGrassmannian_iff k d r hr x).mp hx
      change ∑ j, g i j * x j = 0
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j.val < r
      · rw [hblock i j hi hj, zero_mul]
      · rw [hxzero j (Nat.le_of_not_gt hj), mul_zero]
    · change Module.finrank k
          (P.map (LinearMap.GeneralLinearGroup.toLinearEquiv e).toLinearMap) =
        Module.finrank k P
      exact LinearEquiv.finrank_map_eq
        (LinearMap.GeneralLinearGroup.toLinearEquiv e) P
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
