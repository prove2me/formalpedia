-- Prove2me | solution 1 for PolygonalPathConstant
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T19:30:22.575149+00:00
-- url     : https://prove2.me/submissions/7f63300d-5c57-4a26-89c7-25c710635dc3

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

theorem solution (p : EuclideanSpace ℝ (Fin 2)) :
    ∃ γ : PolygonalPath,
      γ.source = p ∧
        γ.target = p ∧
          γ.carrier = ({p} : Set (EuclideanSpace ℝ (Fin 2))) := by
  let γ : PolygonalPath :=
    { vertices := [p]
      vertices_nonempty := by simp
      source := p
      target := p
      source_eq_head := by simp
      target_eq_last := by simp
      carrier := ({p} : Set (EuclideanSpace ℝ (Fin 2)))
      carrier_eq := by
        ext q
        simp }
  exact ⟨γ, rfl, rfl, rfl⟩
