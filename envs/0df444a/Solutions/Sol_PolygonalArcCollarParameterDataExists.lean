-- Prove2me | solution 1 for PolygonalArcCollarParameterDataExists
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T02:23:34.356985+00:00
-- url     : https://prove2.me/submissions/74f7b6db-edda-43c8-8401-2bc829fd8662

import Definitions.Def_PolygonalArcCollarParameterData
import Theorems.Thm_PlanarRot90Norm
import Theorems.Thm_PlanarRot90Orthogonal
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarParameterDataExists]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists, parameter/normal phase.
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L109-L332
 theorem solution (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins) := by
  let leftParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let rightParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    1 - controlRadii.radius ⟨j + 1, hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let segmentLength : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    dist γ.vertices[j] γ.vertices[j + 1]
  let paramSlack : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (leftParam j hj / 2)
      (min ((1 - rightParam j hj) / 2)
        (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1))))
  let lowerParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    leftParam j hj - paramSlack j hj
  let upperParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    rightParam j hj + paramSlack j hj
  let normal : (j : ℕ) → j + 1 < γ.vertices.length →
      EuclideanSpace ℝ (Fin 2) := fun j hj =>
    PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])
  have leftParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < leftParam j hj := by
    intro j hj
    simpa [leftParam] using middleSegments.left_parameter_pos j hj
  have leftParam_lt_rightParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftParam j hj < rightParam j hj := by
    intro j hj
    simpa [leftParam, rightParam] using
      middleSegments.left_parameter_lt_right_parameter j hj
  have rightParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightParam j hj < 1 := by
    intro j hj
    simpa [rightParam] using middleSegments.right_parameter_lt_one j hj
  have one_sub_rightParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < 1 - rightParam j hj := by
    intro j hj
    linarith [rightParam_lt_one j hj]
  have segmentLength_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < segmentLength j hj := by
    intro j hj
    let i0 : Fin γ.vertices.length := ⟨j, Nat.lt_of_succ_lt hj⟩
    let i1 : Fin γ.vertices.length := ⟨j + 1, hj⟩
    have hleft : 0 < controlRadii.radius i0 := controlRadii.radius_pos i0
    have hright : 0 < controlRadii.radius i1 := controlRadii.radius_pos i1
    have hsum :
        controlRadii.radius i0 + controlRadii.radius i1 <
          dist γ.vertices[j] γ.vertices[j + 1] := by
      simpa [i0, i1] using controlRadii.adjacent_radii_sum_lt (j := j) hj
    dsimp [segmentLength]
    nlinarith
  have paramSlack_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < paramSlack j hj := by
    intro j hj
    have hden : 0 < 8 * (segmentLength j hj + 1) := by
      have hD : 0 < segmentLength j hj := segmentLength_pos j hj
      positivity
    dsimp [paramSlack]
    exact lt_min (half_pos (leftParam_pos j hj))
      (lt_min (half_pos (one_sub_rightParam_pos j hj))
        (div_pos (forbiddenMargins.margin_pos j hj) hden))
  have paramSlack_le_left_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ leftParam j hj / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact min_le_left _ _
  have paramSlack_le_one_sub_right_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ (1 - rightParam j hj) / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have paramSlack_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have paramSlack_mul_segmentLength_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj * segmentLength j hj <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    let D : ℝ := segmentLength j hj
    let μ : ℝ := forbiddenMargins.margin j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hμpos : 0 < μ := by
      dsimp [μ]
      exact forbiddenMargins.margin_pos j hj
    have hdenpos : 0 < 8 * (D + 1) := by positivity
    have hscaled :
        μ / (8 * (D + 1)) * D < μ / 4 := by
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      paramSlack j hj * segmentLength j hj
          ≤ (μ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by
                simpa [D, μ] using paramSlack_le_margin_scaled j hj)
              hDnonneg
      _ < μ / 4 := hscaled
  have lowerParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj := by
    intro j hj
    have hle := paramSlack_le_left_half j hj
    have hleft := leftParam_pos j hj
    dsimp [lowerParam]
    nlinarith
  have lowerParam_lt_leftParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        lowerParam j hj < leftParam j hj := by
    intro j hj
    dsimp [lowerParam]
    linarith [paramSlack_pos j hj]
  have rightParam_lt_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < upperParam j hj := by
    intro j hj
    dsimp [upperParam]
    linarith [paramSlack_pos j hj]
  have upperParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1 := by
    intro j hj
    have hle := paramSlack_le_one_sub_right_half j hj
    have hright := rightParam_lt_one j hj
    dsimp [upperParam]
    nlinarith
  have one_sub_upperParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < 1 - upperParam j hj := by
    intro j hj
    linarith [upperParam_lt_one j hj]
  have normal_orthogonal :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        inner ℝ (γ.vertices[j + 1] - γ.vertices[j]) (normal j hj) = 0 := by
    intro j hj
    simpa [normal] using PlanarRot90Orthogonal (γ.vertices[j + 1] - γ.vertices[j])
  have normal_norm_eq_tangent_norm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = ‖γ.vertices[j + 1] - γ.vertices[j]‖ := by
    intro j hj
    simpa [normal] using PlanarRot90Norm (γ.vertices[j + 1] - γ.vertices[j])
  have normal_norm_eq_segmentLength :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = segmentLength j hj := by
    intro j hj
    calc
      ‖normal j hj‖ = ‖γ.vertices[j + 1] - γ.vertices[j]‖ :=
        normal_norm_eq_tangent_norm j hj
      _ = ‖γ.vertices[j] - γ.vertices[j + 1]‖ := by
        rw [← norm_neg (γ.vertices[j + 1] - γ.vertices[j])]
        congr 1
        abel
      _ = dist γ.vertices[j] γ.vertices[j + 1] := by
        rw [dist_eq_norm]
      _ = segmentLength j hj := by
        rfl
  exact ⟨{
    leftParam := leftParam
    rightParam := rightParam
    segmentLength := segmentLength
    paramSlack := paramSlack
    lowerParam := lowerParam
    upperParam := upperParam
    normal := normal
    leftParam_eq := by
      intro j hj
      rfl
    rightParam_eq := by
      intro j hj
      rfl
    segmentLength_eq := by
      intro j hj
      rfl
    paramSlack_eq := by
      intro j hj
      rfl
    lowerParam_eq := by
      intro j hj
      rfl
    upperParam_eq := by
      intro j hj
      rfl
    normal_eq_positive_quarter_turn := by
      intro j hj
      rfl
    leftParam_pos := leftParam_pos
    leftParam_lt_rightParam := leftParam_lt_rightParam
    rightParam_lt_one := rightParam_lt_one
    paramSlack_pos := paramSlack_pos
    paramSlack_mul_segmentLength_lt_margin_quarter :=
      paramSlack_mul_segmentLength_lt_margin_quarter
    lowerParam_pos := lowerParam_pos
    lowerParam_lt_leftParam := lowerParam_lt_leftParam
    rightParam_lt_upperParam := rightParam_lt_upperParam
    upperParam_lt_one := upperParam_lt_one
    one_sub_upperParam_pos := one_sub_upperParam_pos
    normal_orthogonal := normal_orthogonal
    normal_norm_eq_segmentLength := normal_norm_eq_segmentLength
    segmentLength_pos := segmentLength_pos
  }⟩
