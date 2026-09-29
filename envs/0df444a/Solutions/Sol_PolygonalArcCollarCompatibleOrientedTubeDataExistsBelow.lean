-- Prove2me | solution 1 for PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T00:31:52.58152+00:00
-- url     : https://prove2.me/submissions/42c8e4a0-fbfb-4ea7-98f3-e6f252b5f81b

import Mathlib.Tactic
import Theorems.Thm_PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement
import Theorems.Thm_PolygonalArcCollarCompatibleOrientedTubeDataExists

open Classical
noncomputable section

theorem solution (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
      0 < K₁ →
        let hfirst : 0 + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        let jlast : ℕ := γ.vertices.length - 2
        let hlast : jlast + 1 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          dsimp [jlast]
          omega
        ∃ compatibleTubes :
          PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii
            middleSegments forbiddenMargins,
          compatibleTubes.initialConeBound 0 hfirst < K₀ ∧
            compatibleTubes.terminalConeBound jlast hlast < K₁ ∧
              (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ 0 →
                Disjoint
                  (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                    j hj)
                  (Metric.ball γ.source r₀)) ∧
                (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), j ≠ jlast →
                  Disjoint
                    (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
                      j hj)
                    (Metric.ball γ.target r₁)) := by
  intro hIso hK₀ hK₁
  obtain ⟨base⟩ :=
    PolygonalArcCollarCompatibleOrientedTubeDataExists γ controlRadii middleSegments
      forbiddenMargins
  exact
    PolygonalArcCollarCompatibleOrientedTubeDataEndpointRefinement
      (γ := γ) (controlRadii := controlRadii) (middleSegments := middleSegments)
      (forbiddenMargins := forbiddenMargins) (base := base)
      (r₀ := r₀) (r₁ := r₁) (K₀ := K₀) (K₁ := K₁)
      hIso hK₀ hK₁
