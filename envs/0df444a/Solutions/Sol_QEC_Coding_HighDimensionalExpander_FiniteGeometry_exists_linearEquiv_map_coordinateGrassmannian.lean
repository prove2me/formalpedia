-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.exists_linearEquiv_map_coordinateGrassmannian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:25:18.69672+00:00
-- url     : https://prove2.me/submissions/97ce8eb7-41d2-43d8-bf03-b671d2613908

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (W : FiniteGrassmannian k (Fin d → k) r) :
    ∃ g : (Fin d → k) ≃ₗ[k] (Fin d → k),
      (coordinateGrassmannian k d r hr).1.map g.toLinearMap = W.1 := by
  let P := (coordinateGrassmannian k d r hr).1
  let f : P ≃ₗ[k] W.1 := LinearEquiv.ofFinrankEq _ _ (by
    rw [show Module.finrank k P = r from (coordinateGrassmannian k d r hr).property,
      W.property])
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g y ∈ W.1
    rw [← hg ⟨y, hy⟩]
    exact (f ⟨y, hy⟩).property
  · intro hx
    let y : P := f.symm ⟨x, hx⟩
    refine ⟨y, y.property, ?_⟩
    change g (y : Fin d → k) = x
    rw [← hg y]
    simp [y]
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
