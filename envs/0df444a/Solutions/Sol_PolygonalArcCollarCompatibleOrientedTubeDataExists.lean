-- Prove2me | solution 1 for PolygonalArcCollarCompatibleOrientedTubeDataExists
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T02:13:09.624956+00:00
-- url     : https://prove2.me/submissions/b1546ba4-f730-4337-9a11-f9341f8b9126

import Theorems.Thm_PolygonalArcCollarParameterDataExists
import Theorems.Thm_PolygonalArcCollarCenterlineSeparationDataExists
import Theorems.Thm_PolygonalArcCollarOrientedTubeWitnessExists
import Theorems.Thm_PolygonalArcCollarConeSeparationDataExists
import Theorems.Thm_PolygonalArcAdjacentOutwardDirectionsNotSameRay
import Theorems.Thm_PlanarRot90ConeAvoidsRay
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarCompatibleOrientedTubeDataExists]
-- Final assembly of the four source-phase interfaces.
theorem solution (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins) := by
  obtain ⟨parameters⟩ :=
    PolygonalArcCollarParameterDataExists γ controlRadii middleSegments forbiddenMargins
  obtain ⟨separations⟩ :=
    PolygonalArcCollarCenterlineSeparationDataExists γ controlRadii middleSegments
      forbiddenMargins parameters
  obtain ⟨cones⟩ :=
    PolygonalArcCollarConeSeparationDataExists γ controlRadii middleSegments forbiddenMargins
  obtain ⟨witness⟩ :=
    PolygonalArcCollarOrientedTubeWitnessExists γ controlRadii middleSegments
      forbiddenMargins parameters separations cones.initialConeBound cones.terminalConeBound
      cones.initialConeBound_pos cones.terminalConeBound_pos
  refine ⟨
    { orientedTubes := witness.orientedTubes
      initialConeBound := cones.initialConeBound
      terminalConeBound := cones.terminalConeBound
      initialConeBound_pos := cones.initialConeBound_pos
      terminalConeBound_pos := cones.terminalConeBound_pos
      initial_halfWidth_lt_cone_mul_lowerParam :=
        witness.initial_halfWidth_lt_cone_mul_lowerParam
      terminal_halfWidth_lt_cone_mul_one_sub_upperParam :=
        witness.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
      initial_signed_cone_disjoint_previous_segment := by
        intro j hj hprev
        have hnormal :
            witness.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj =
              PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
          simpa [PlanarRot90] using
            witness.orientedTubes.normal_eq_positive_quarter_turn j hj
        rw [hnormal]
        exact cones.initial_signed_cone_disjoint_previous_segment j hj hprev
      terminal_signed_cone_disjoint_next_segment := by
        intro j hj hnext
        have hnormal :
            witness.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj =
              PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
          simpa [PlanarRot90] using
            witness.orientedTubes.normal_eq_positive_quarter_turn j hj
        rw [hnormal]
        exact cones.terminal_signed_cone_disjoint_next_segment j hj hnext
      successive_positive_negative_cones_disjoint := by
        intro j hj hnext
        have hnormal₀ :
            witness.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj =
              PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
          simpa [PlanarRot90] using
            witness.orientedTubes.normal_eq_positive_quarter_turn j hj
        have hnormal₁ :
            witness.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal (j + 1) hnext =
              PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
          simpa [PlanarRot90] using
            witness.orientedTubes.normal_eq_positive_quarter_turn (j + 1) hnext
        rw [hnormal₀, hnormal₁]
        exact cones.successive_positive_negative_cones_disjoint j hj hnext
      successive_negative_positive_cones_disjoint := by
        intro j hj hnext
        have hnormal₀ :
            witness.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj =
              PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
          simpa [PlanarRot90] using
            witness.orientedTubes.normal_eq_positive_quarter_turn j hj
        have hnormal₁ :
            witness.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal (j + 1) hnext =
              PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
          simpa [PlanarRot90] using
            witness.orientedTubes.normal_eq_positive_quarter_turn (j + 1) hnext
        rw [hnormal₀, hnormal₁]
        exact cones.successive_negative_positive_cones_disjoint j hj hnext
      initialAwaySeparation := separations.initialAwaySeparation
      terminalAwaySeparation := separations.terminalAwaySeparation
      successiveAwaySeparation := separations.successiveAwaySeparation
      initialAwaySeparation_pos := separations.initialAwaySeparation_pos
      terminalAwaySeparation_pos := separations.terminalAwaySeparation_pos
      successiveAwaySeparation_pos := separations.successiveAwaySeparation_pos
      initial_centerline_previous_segment_away :=
        separations.initial_centerline_previous_segment_away
      terminal_centerline_next_segment_away :=
        separations.terminal_centerline_next_segment_away
      successive_centerlines_away := separations.successive_centerlines_away
      initial_halfWidth_mul_normal_norm_lt_away_quarter :=
        witness.initial_halfWidth_mul_normal_norm_lt_away_quarter
      terminal_halfWidth_mul_normal_norm_lt_away_quarter :=
        witness.terminal_halfWidth_mul_normal_norm_lt_away_quarter
      successive_halfWidth_normal_sum_lt_away_quarter :=
        witness.successive_halfWidth_normal_sum_lt_away_quarter }⟩
