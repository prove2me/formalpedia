-- Prove2me | solution 1 for PolygonalArcCollarOrientedTubeWitnessExists
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T03:17:23.526851+00:00
-- url     : https://prove2.me/submissions/17c878cb-d567-4e8d-a595-42d5e3c7f9bc

import Definitions.Def_PolygonalArcCollarOrientedTubeWitness
import Theorems.Thm_PlanarRot90Norm
import Theorems.Thm_PlanarRot90Orthogonal
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

open Classical
noncomputable section

set_option maxHeartbeats 3000000

-- [TABLET NODE: PolygonalArcCollarOrientedTubeWitnessExists]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists,
-- exact half-width/tube construction and oriented-separated-tube packaging.
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L614-L1189,L1463-L1683
 theorem solution (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (parameters :
      PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins)
    (separations :
      PolygonalArcCollarCenterlineSeparationData γ controlRadii middleSegments
        forbiddenMargins parameters)
    (initialConeBound terminalConeBound :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ)
    (initialConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < initialConeBound j hj)
    (terminalConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < terminalConeBound j hj) :
    Nonempty
      (PolygonalArcCollarOrientedTubeWitness γ controlRadii middleSegments
        forbiddenMargins parameters separations initialConeBound terminalConeBound
        initialConeBound_pos terminalConeBound_pos) := by
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
  have leftParam_matches :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftParam j hj = parameters.leftParam j hj := by
    intro j hj
    simpa [leftParam] using (parameters.leftParam_eq j hj).symm
  have rightParam_matches :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj = parameters.rightParam j hj := by
    intro j hj
    simpa [rightParam] using (parameters.rightParam_eq j hj).symm
  have segmentLength_matches :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        segmentLength j hj = parameters.segmentLength j hj := by
    intro j hj
    simpa [segmentLength] using (parameters.segmentLength_eq j hj).symm
  have paramSlack_matches :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj = parameters.paramSlack j hj := by
    intro j hj
    calc
      paramSlack j hj =
          min (leftParam j hj / 2)
            (min ((1 - rightParam j hj) / 2)
              (forbiddenMargins.margin j hj /
                (8 * (segmentLength j hj + 1)))) := by rfl
      _ = min (parameters.leftParam j hj / 2)
            (min ((1 - parameters.rightParam j hj) / 2)
              (forbiddenMargins.margin j hj /
                (8 * (parameters.segmentLength j hj + 1)))) := by
          rw [leftParam_matches j hj, rightParam_matches j hj,
            segmentLength_matches j hj]
      _ = parameters.paramSlack j hj :=
        (parameters.paramSlack_eq j hj).symm
  have lowerParam_matches :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        lowerParam j hj = parameters.lowerParam j hj := by
    intro j hj
    calc
      lowerParam j hj = leftParam j hj - paramSlack j hj := rfl
      _ = parameters.leftParam j hj - parameters.paramSlack j hj := by
        rw [leftParam_matches j hj, paramSlack_matches j hj]
      _ = parameters.lowerParam j hj := (parameters.lowerParam_eq j hj).symm
  have upperParam_matches :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        upperParam j hj = parameters.upperParam j hj := by
    intro j hj
    calc
      upperParam j hj = rightParam j hj + paramSlack j hj := rfl
      _ = parameters.rightParam j hj + parameters.paramSlack j hj := by
        rw [rightParam_matches j hj, paramSlack_matches j hj]
      _ = parameters.upperParam j hj := (parameters.upperParam_eq j hj).symm
  have normal_matches :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        normal j hj = parameters.normal j hj := by
    intro j hj
    simpa [normal] using (parameters.normal_eq_positive_quarter_turn j hj).symm
  have leftParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < leftParam j hj := by
    intro j hj
    rw [leftParam_matches j hj]
    exact parameters.leftParam_pos j hj
  have leftParam_lt_rightParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftParam j hj < rightParam j hj := by
    intro j hj
    rw [leftParam_matches j hj, rightParam_matches j hj]
    exact parameters.leftParam_lt_rightParam j hj
  have rightParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightParam j hj < 1 := by
    intro j hj
    rw [rightParam_matches j hj]
    exact parameters.rightParam_lt_one j hj
  have one_sub_rightParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < 1 - rightParam j hj := by
    intro j hj
    linarith [rightParam_lt_one j hj]
  have segmentLength_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < segmentLength j hj := by
    intro j hj
    rw [segmentLength_matches j hj]
    exact parameters.segmentLength_pos j hj
  have paramSlack_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < paramSlack j hj := by
    intro j hj
    rw [paramSlack_matches j hj]
    exact parameters.paramSlack_pos j hj
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
    rw [paramSlack_matches j hj, segmentLength_matches j hj]
    exact parameters.paramSlack_mul_segmentLength_lt_margin_quarter j hj
  have lowerParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj := by
    intro j hj
    rw [lowerParam_matches j hj]
    exact parameters.lowerParam_pos j hj
  have lowerParam_lt_leftParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        lowerParam j hj < leftParam j hj := by
    intro j hj
    rw [lowerParam_matches j hj, leftParam_matches j hj]
    exact parameters.lowerParam_lt_leftParam j hj
  have rightParam_lt_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < upperParam j hj := by
    intro j hj
    rw [rightParam_matches j hj, upperParam_matches j hj]
    exact parameters.rightParam_lt_upperParam j hj
  have upperParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1 := by
    intro j hj
    rw [upperParam_matches j hj]
    exact parameters.upperParam_lt_one j hj
  have one_sub_upperParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < 1 - upperParam j hj := by
    intro j hj
    linarith [upperParam_lt_one j hj]
  have eta_pos : 0 < η := by
    have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
    have hidx : (0 : ℕ) < γ.vertices.length := by omega
    exact (controlRadii.radius_pos ⟨0, hidx⟩).trans
      (controlRadii.radius_lt_eta ⟨0, hidx⟩)
  let initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ :=
    fun j hj hprev => separations.initialAwaySeparation j hj hprev
  let terminalAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => separations.terminalAwaySeparation j hj hnext
  let successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => separations.successiveAwaySeparation j hj hnext
  have initialAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        0 < initialAwaySeparation j hj hprev := by
    intro j hj hprev
    dsimp [initialAwaySeparation]
    exact separations.initialAwaySeparation_pos j hj hprev
  have terminalAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < terminalAwaySeparation j hj hnext := by
    intro j hj hnext
    dsimp [terminalAwaySeparation]
    exact separations.terminalAwaySeparation_pos j hj hnext
  have successiveAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < successiveAwaySeparation j hj hnext := by
    intro j hj hnext
    dsimp [successiveAwaySeparation]
    exact separations.successiveAwaySeparation_pos j hj hnext

  let initialAwayWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hprev : 0 < j then
        initialAwaySeparation j hj hprev / (8 * (segmentLength j hj + 1))
      else
        1
  let terminalAwayWidthTerm : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj =>
      if hnext : (j + 1) + 1 < γ.vertices.length then
        terminalAwaySeparation j hj hnext / (8 * (segmentLength j hj + 1))
      else
        1
  let previousSuccessiveAwayWidthTerm :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      successiveAwaySeparation (j - 1)
          (by
            have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
          (by
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj) /
        (16 * (segmentLength j hj + 1))
    else
      1
  let nextSuccessiveAwayWidthTerm :
      (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      successiveAwaySeparation j hj hnext / (16 * (segmentLength j hj + 1))
    else
      1
  let halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min
      (min (η / (4 * (segmentLength j hj + 1)))
        (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1))))
      (min
        (min (initialConeBound j hj * lowerParam j hj / 2)
          (terminalConeBound j hj * (1 - upperParam j hj) / 2))
        (min
          (min (initialAwayWidthTerm j hj) (terminalAwayWidthTerm j hj))
          (min (previousSuccessiveAwayWidthTerm j hj)
            (nextSuccessiveAwayWidthTerm j hj))))
  let tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let leftHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let rightHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (0 : ℝ) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  have initialAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < initialAwayWidthTerm j hj := by
    intro j hj
    dsimp [initialAwayWidthTerm]
    by_cases hprev : 0 < j
    · have hden : 0 < 8 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hprev] using
        div_pos (initialAwaySeparation_pos j hj hprev) hden
    · simp [hprev]
  have terminalAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < terminalAwayWidthTerm j hj := by
    intro j hj
    dsimp [terminalAwayWidthTerm]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · have hden : 0 < 8 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hnext] using
        div_pos (terminalAwaySeparation_pos j hj hnext) hden
    · simp [hnext]
  have previousSuccessiveAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < previousSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [previousSuccessiveAwayWidthTerm]
    by_cases hprev : 0 < j
    · have hden : 0 < 16 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hprev] using
        div_pos
          (successiveAwaySeparation_pos (j - 1)
            (by
              have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
            (by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))
          hden
    · simp [hprev]
  have nextSuccessiveAwayWidthTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < nextSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [nextSuccessiveAwayWidthTerm]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · have hden : 0 < 16 * (segmentLength j hj + 1) := by
        have hD := segmentLength_pos j hj
        positivity
      simpa [hnext] using
        div_pos (successiveAwaySeparation_pos j hj hnext) hden
    · simp [hnext]
  have halfWidth_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < halfWidth j hj := by
    intro j hj
    have hD : 0 < segmentLength j hj := segmentLength_pos j hj
    have hden4 : 0 < 4 * (segmentLength j hj + 1) := by positivity
    have hden8 : 0 < 8 * (segmentLength j hj + 1) := by positivity
    have hconeI :
        0 < initialConeBound j hj * lowerParam j hj / 2 := by
      exact half_pos (mul_pos (initialConeBound_pos j hj) (lowerParam_pos j hj))
    have hconeT :
        0 < terminalConeBound j hj * (1 - upperParam j hj) / 2 := by
      exact half_pos
        (mul_pos (terminalConeBound_pos j hj) (one_sub_upperParam_pos j hj))
    dsimp [halfWidth]
    exact lt_min
      (lt_min (div_pos eta_pos hden4)
        (div_pos (forbiddenMargins.margin_pos j hj) hden8))
      (lt_min (lt_min hconeI hconeT)
        (lt_min
          (lt_min (initialAwayWidthTerm_pos j hj) (terminalAwayWidthTerm_pos j hj))
          (lt_min (previousSuccessiveAwayWidthTerm_pos j hj)
            (nextSuccessiveAwayWidthTerm_pos j hj))))
  have halfWidth_le_eta_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ η / (4 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have halfWidth_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have halfWidth_le_initialConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ initialConeBound j hj * lowerParam j hj / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have halfWidth_le_terminalConeWidth :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ terminalConeBound j hj * (1 - upperParam j hj) / 2 := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have halfWidth_le_initialAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ initialAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_left _ _)))
  have halfWidth_le_terminalAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ terminalAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _)))
  have halfWidth_le_previousSuccessiveAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ previousSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
  have halfWidth_le_nextSuccessiveAwayWidthTerm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ nextSuccessiveAwayWidthTerm j hj := by
    intro j hj
    dsimp [halfWidth]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  have halfWidth_lt_initialCone_mul_lowerParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < initialConeBound j hj * lowerParam j hj := by
    intro j hj
    have hprod : 0 < initialConeBound j hj * lowerParam j hj :=
      mul_pos (initialConeBound_pos j hj) (lowerParam_pos j hj)
    have hhalf :
        initialConeBound j hj * lowerParam j hj / 2 <
          initialConeBound j hj * lowerParam j hj := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_initialConeWidth j hj) hhalf
  have halfWidth_lt_terminalCone_mul_one_sub_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj < terminalConeBound j hj * (1 - upperParam j hj) := by
    intro j hj
    have hprod : 0 < terminalConeBound j hj * (1 - upperParam j hj) :=
      mul_pos (terminalConeBound_pos j hj) (one_sub_upperParam_pos j hj)
    have hhalf :
        terminalConeBound j hj * (1 - upperParam j hj) / 2 <
          terminalConeBound j hj * (1 - upperParam j hj) := by
      nlinarith
    exact lt_of_le_of_lt (halfWidth_le_terminalConeWidth j hj) hhalf
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
  have normal_norm_eq_segment_length :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = dist γ.vertices[j] γ.vertices[j + 1] := by
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
  have halfWidth_mul_normal_norm_lt_eta :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ < η := by
    intro j hj
    let D : ℝ := segmentLength j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hdenpos : 0 < 4 * (D + 1) := by positivity
    have hscaled : η / (4 * (D + 1)) * D < η := by
      have hden_ne : 4 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (η / (4 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [D] using halfWidth_le_eta_scaled j hj) hDnonneg
      _ < η := hscaled
  have halfWidth_mul_normal_norm_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ <
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
    have hscaled : μ / (8 * (D + 1)) * D < μ / 4 := by
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (μ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [D, μ] using halfWidth_le_margin_scaled j hj) hDnonneg
      _ < μ / 4 := hscaled
  have dist_lineMap_lineMap_local :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (c₁ c₂ : ℝ),
        dist (AffineMap.lineMap A B c₁) (AffineMap.lineMap A B c₂) =
          dist c₁ c₂ * dist A B := by
    intro A B c₁ c₂
    rw [dist_eq_norm, Real.dist_eq, dist_eq_norm]
    have hvec :
        AffineMap.lineMap A B c₁ - AffineMap.lineMap A B c₂ =
          (c₁ - c₂) • (B - A) := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    rw [hvec, norm_smul, Real.norm_eq_abs]
    have hnorm : ‖B - A‖ = ‖A - B‖ := by
      have hneg : B - A = -(A - B) := by
        abel
      rw [hneg, norm_neg]
    rw [hnorm]
  have real_dist_to_Icc_of_mem_Ioo_expansion :
      ∀ {L R ε t : ℝ}, 0 < ε → L < R →
        t ∈ Set.Ioo (L - ε) (R + ε) →
          ∃ u : ℝ, u ∈ Set.Icc L R ∧ dist t u < ε := by
    intro L R ε t hε hLR ht
    by_cases htL : t < L
    · refine ⟨L, ⟨le_rfl, le_of_lt hLR⟩, ?_⟩
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htL)]
      linarith [ht.1]
    · by_cases htR : t ≤ R
      · refine ⟨t, ⟨le_of_not_gt htL, htR⟩, ?_⟩
        simpa using hε
      · have hRt : R < t := lt_of_not_ge htR
        refine ⟨R, ⟨le_of_lt hLR, le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hRt)]
        linarith [ht.2]
  have middle_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        middleSegments.middle j hj ⊆ tube j hj := by
    intro j hj z hz
    rw [middleSegments.middle_eq j hj] at hz
    rcases hz with ⟨t, ht, rfl⟩
    rw [show tube j hj =
        {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
          ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj} by rfl]
    refine ⟨t, ?_, 0, ?_, by simp⟩
    · exact ⟨(lowerParam_lt_leftParam j hj).trans_le ht.1,
        lt_of_le_of_lt ht.2 (rightParam_lt_upperParam j hj)⟩
    · exact ⟨by simpa using halfWidth_pos j hj, halfWidth_pos j hj⟩
  have leftHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [leftHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨lt_trans (neg_neg_of_pos (halfWidth_pos j hj)) hs.1, hs.2⟩
  have rightHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [rightHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨hs.1, hs.2.trans (halfWidth_pos j hj)⟩
  have tube_subset_eta_neighborhood :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ γ.carrier, dist z p < η := by
    intro j hj z hz
    dsimp [tube] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    let p : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
    have hpseg : p ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      refine ⟨t, ?_, rfl⟩
      exact ⟨le_of_lt ((lowerParam_pos j hj).trans ht.1),
        le_of_lt (ht.2.trans (upperParam_lt_one j hj))⟩
    have hpcarrier : p ∈ γ.carrier := by
      rw [γ.carrier_eq]
      exact ⟨j, hj, hpseg⟩
    refine ⟨p, hpcarrier, ?_⟩
    have hs_abs : |s| < halfWidth j hj := abs_lt.mpr hs
    have hdist :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p = |s| * ‖normal j hj‖ := by
      have hsub :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj - p =
            s • normal j hj := by
        simp [p]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc
      dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p = |s| * ‖normal j hj‖ := hdist
      _ ≤ halfWidth j hj * ‖normal j hj‖ := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
      _ < η := halfWidth_mul_normal_norm_lt_eta j hj
  have tube_point_close_to_middle :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
          dist z p < forbiddenMargins.margin j hj / 2 := by
    intro j hj z hz
    dsimp [tube] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    obtain ⟨u, huIcc, htu⟩ :=
      real_dist_to_Icc_of_mem_Ioo_expansion
        (L := leftParam j hj) (R := rightParam j hj)
        (ε := paramSlack j hj) (t := t) (paramSlack_pos j hj)
        (leftParam_lt_rightParam j hj) (by
          simpa [lowerParam, upperParam] using ht)
    let p : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] u
    have hpM : p ∈ middleSegments.middle j hj := by
      rw [middleSegments.middle_eq j hj]
      exact ⟨u, by simpa [leftParam, rightParam] using huIcc, rfl⟩
    refine ⟨p, hpM, ?_⟩
    let q : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
    have hs_abs : |s| < halfWidth j hj := abs_lt.mpr hs
    have hperp :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q = |s| * ‖normal j hj‖ := by
      have hsub :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj - q =
            s • normal j hj := by
        simp [q]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    have hperp_lt :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q <
          forbiddenMargins.margin j hj / 4 := by
      calc
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q = |s| * ‖normal j hj‖ := hperp
        _ ≤ halfWidth j hj * ‖normal j hj‖ := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
        _ < forbiddenMargins.margin j hj / 4 :=
          halfWidth_mul_normal_norm_lt_margin_quarter j hj
    have hline_lt : dist q p < forbiddenMargins.margin j hj / 4 := by
      have htuD :
          dist t u * segmentLength j hj <
            forbiddenMargins.margin j hj / 4 := by
        have hmul :
            dist t u * segmentLength j hj <
              paramSlack j hj * segmentLength j hj :=
          mul_lt_mul_of_pos_right htu (segmentLength_pos j hj)
        exact hmul.trans (paramSlack_mul_segmentLength_lt_margin_quarter j hj)
      calc
        dist q p =
            dist t u * dist γ.vertices[j] γ.vertices[j + 1] := by
              simpa [q, p] using
                dist_lineMap_lineMap_local γ.vertices[j] γ.vertices[j + 1] t u
        _ = dist t u * segmentLength j hj := by
              simp [segmentLength]
        _ < forbiddenMargins.margin j hj / 4 := htuD
    have htri :
        dist
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj) p ≤
          dist
              (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj) q +
            dist q p :=
      dist_triangle _ _ _
    calc
      dist
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p
          ≤
        dist
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj) q +
          dist q p := htri
      _ < forbiddenMargins.margin j hj / 4 +
          forbiddenMargins.margin j hj / 4 := add_lt_add hperp_lt hline_lt
      _ = forbiddenMargins.margin j hj / 2 := by ring
  have tube_disjoint_nonadjacent_segments :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzSeg
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
    have hmargin :=
      forbiddenMargins.middle_segment_separation j hj k hk hgap p hpM z hzSeg
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']
  have tube_disjoint_nonincident_control_disks :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (i : Fin γ.vertices.length),
          i.1 ≠ j → i.1 ≠ j + 1 →
            Disjoint (tube j hj)
              (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)) := by
    intro j hj i hij hijs
    rw [Set.disjoint_left]
    intro z hzTube hzDisk
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
    have hmargin :=
      forbiddenMargins.middle_control_disk_separation j hj i hij hijs p hpM z hzDisk
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']
  have tube_disjoint_nonadjacent_middle_cores :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (middleSegments.middle k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzMiddle
    exact Set.disjoint_left.mp
      (tube_disjoint_nonadjacent_segments j hj k hk hgap) hzTube
      (middleSegments.middle_subset_segment k hk hzMiddle)
  have tube_disjoint_nonadjacent_tubes :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (tube k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzj hzk
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzj
    obtain ⟨q, hqM, hqClose⟩ := tube_point_close_to_middle k hk z hzk
    have hgap_sym : k + 1 < j ∨ j + 1 < k := by
      cases hgap with
      | inl h => exact Or.inr h
      | inr h => exact Or.inl h
    have hmj :=
      forbiddenMargins.middle_core_separation j hj k hk hgap p hpM q hqM
    have hmk :=
      forbiddenMargins.middle_core_separation k hk j hj hgap_sym q hqM p hpM
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    have hmk' : forbiddenMargins.margin k hk ≤ dist p q := by
      simpa [dist_comm] using hmk
    have htri : dist p q ≤ dist p z + dist z q := dist_triangle p z q
    have hsum :
        dist p q <
          forbiddenMargins.margin j hj / 2 +
            forbiddenMargins.margin k hk / 2 :=
      lt_of_le_of_lt htri (add_lt_add hpClose' hqClose)
    nlinarith [forbiddenMargins.margin_pos j hj,
      forbiddenMargins.margin_pos k hk, hmj, hmk', hsum]
  have initial_centerline_previous_segment_away :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∀ t : ℝ,
          t ∈ Set.Icc
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) →
          ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
            initialAwaySeparation j hj hprev ≤
              dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hprev t ht q hq
    exact separations.initial_centerline_previous_segment_away j hj hprev t ht q hq
  have terminal_centerline_next_segment_away :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ t : ℝ,
            t ∈ Set.Icc (0 : ℝ)
              (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
              terminalAwaySeparation j hj hnext ≤
                dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hnext t ht q hq
    exact separations.terminal_centerline_next_segment_away j hj hnext t ht q hq
  have successive_centerlines_away :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ t : ℝ,
            t ∈ Set.Icc (0 : ℝ)
              (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ u : ℝ,
              u ∈ Set.Icc
                (controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j + 1] γ.vertices[j + 2]) (1 : ℝ) →
                successiveAwaySeparation j hj hnext ≤
                  dist
                    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u) := by
    intro j hj hnext t ht u hu
    exact separations.successive_centerlines_away j hj hnext t ht u hu

  have initial_halfWidth_mul_normal_norm_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        halfWidth j hj * ‖normal j hj‖ <
          initialAwaySeparation j hj hprev / 4 := by
    intro j hj hprev
    let D : ℝ := segmentLength j hj
    let δ : ℝ := initialAwaySeparation j hj hprev
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact initialAwaySeparation_pos j hj hprev
    have hscaled : δ / (8 * (D + 1)) * D < δ / 4 := by
      have hdenpos : 0 < 8 * (D + 1) := by positivity
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (δ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by
                dsimp [initialAwayWidthTerm] at halfWidth_le_initialAwayWidthTerm
                simpa [D, δ, hprev] using halfWidth_le_initialAwayWidthTerm j hj)
              hDnonneg
      _ < δ / 4 := hscaled
  have terminal_halfWidth_mul_normal_norm_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj * ‖normal j hj‖ <
            terminalAwaySeparation j hj hnext / 4 := by
    intro j hj hnext
    let D : ℝ := segmentLength j hj
    let δ : ℝ := terminalAwaySeparation j hj hnext
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact terminalAwaySeparation_pos j hj hnext
    have hscaled : δ / (8 * (D + 1)) * D < δ / 4 := by
      have hdenpos : 0 < 8 * (D + 1) := by positivity
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (δ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by
                dsimp [terminalAwayWidthTerm] at halfWidth_le_terminalAwayWidthTerm
                simpa [D, δ, hnext] using halfWidth_le_terminalAwayWidthTerm j hj)
              hDnonneg
      _ < δ / 4 := hscaled
  have successive_halfWidth_normal_sum_lt_away_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          halfWidth j hj * ‖normal j hj‖ +
            halfWidth (j + 1) hnext * ‖normal (j + 1) hnext‖ <
            successiveAwaySeparation j hj hnext / 4 := by
    intro j hj hnext
    let Δ : ℝ := successiveAwaySeparation j hj hnext
    have hΔpos : 0 < Δ := by
      dsimp [Δ]
      exact successiveAwaySeparation_pos j hj hnext
    have left_lt : halfWidth j hj * ‖normal j hj‖ < Δ / 8 := by
      let D : ℝ := segmentLength j hj
      have hDpos : 0 < D := by
        dsimp [D]
        exact segmentLength_pos j hj
      have hDnonneg : 0 ≤ D := le_of_lt hDpos
      have hscaled : Δ / (16 * (D + 1)) * D < Δ / 8 := by
        have hdenpos : 0 < 16 * (D + 1) := by positivity
        have hden_ne : 16 * (D + 1) ≠ 0 := ne_of_gt hdenpos
        field_simp [hden_ne]
        nlinarith
      calc
        halfWidth j hj * ‖normal j hj‖ =
            halfWidth j hj * D := by
              simp [D, segmentLength, normal_norm_eq_segment_length j hj]
        _ ≤ (Δ / (16 * (D + 1))) * D := by
              exact mul_le_mul_of_nonneg_right
                (by
                  dsimp [nextSuccessiveAwayWidthTerm] at halfWidth_le_nextSuccessiveAwayWidthTerm
                  simpa [D, Δ, hnext] using halfWidth_le_nextSuccessiveAwayWidthTerm j hj)
                hDnonneg
        _ < Δ / 8 := hscaled
    have right_lt :
        halfWidth (j + 1) hnext * ‖normal (j + 1) hnext‖ < Δ / 8 := by
      let D : ℝ := segmentLength (j + 1) hnext
      have hDpos : 0 < D := by
        dsimp [D]
        exact segmentLength_pos (j + 1) hnext
      have hDnonneg : 0 ≤ D := le_of_lt hDpos
      have hscaled : Δ / (16 * (D + 1)) * D < Δ / 8 := by
        have hdenpos : 0 < 16 * (D + 1) := by positivity
        have hden_ne : 16 * (D + 1) ≠ 0 := ne_of_gt hdenpos
        field_simp [hden_ne]
        nlinarith
      calc
        halfWidth (j + 1) hnext * ‖normal (j + 1) hnext‖ =
            halfWidth (j + 1) hnext * D := by
              simp [D, segmentLength, normal_norm_eq_segment_length (j + 1) hnext]
        _ ≤ (Δ / (16 * (D + 1))) * D := by
              exact mul_le_mul_of_nonneg_right
                (by
                  dsimp [previousSuccessiveAwayWidthTerm] at halfWidth_le_previousSuccessiveAwayWidthTerm
                  simpa [D, Δ, Nat.succ_pos] using
                    halfWidth_le_previousSuccessiveAwayWidthTerm (j + 1) hnext)
                hDnonneg
        _ < Δ / 8 := hscaled
    nlinarith
  let orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins :=
    { lowerParam := lowerParam
      upperParam := upperParam
      halfWidth := halfWidth
      normal := normal
      tube := tube
      leftHalf := leftHalf
      rightHalf := rightHalf
      lowerParam_pos := lowerParam_pos
      lowerParam_lt_left_parameter := by
        intro j hj
        simpa [leftParam] using lowerParam_lt_leftParam j hj
      right_parameter_lt_upperParam := by
        intro j hj
        simpa [rightParam] using rightParam_lt_upperParam j hj
      upperParam_lt_one := upperParam_lt_one
      halfWidth_pos := halfWidth_pos
      normal_orthogonal := normal_orthogonal
      normal_norm_eq_segment_length := normal_norm_eq_segment_length
      halfWidth_mul_normal_norm_lt_eta := halfWidth_mul_normal_norm_lt_eta
      halfWidth_mul_normal_norm_lt_margin_quarter :=
        halfWidth_mul_normal_norm_lt_margin_quarter
      lower_parameter_slack_mul_segment_length_lt_margin_quarter := by
        intro j hj
        dsimp [lowerParam, leftParam, segmentLength]
        simpa [sub_sub_cancel] using
          paramSlack_mul_segmentLength_lt_margin_quarter j hj
      upper_parameter_slack_mul_segment_length_lt_margin_quarter := by
        intro j hj
        dsimp [upperParam, rightParam, segmentLength]
        simpa [add_sub_cancel_left] using
          paramSlack_mul_segmentLength_lt_margin_quarter j hj
      tube_eq := by
        intro j hj
        rfl
      leftHalf_eq := by
        intro j hj
        rfl
      rightHalf_eq := by
        intro j hj
        rfl
      middle_subset_tube := middle_subset_tube
      leftHalf_subset_tube := leftHalf_subset_tube
      rightHalf_subset_tube := rightHalf_subset_tube
      tube_subset_eta_neighborhood := tube_subset_eta_neighborhood
      tube_point_close_to_middle := tube_point_close_to_middle
      tube_disjoint_nonadjacent_segments := tube_disjoint_nonadjacent_segments
      tube_disjoint_nonincident_control_disks :=
        tube_disjoint_nonincident_control_disks
      tube_disjoint_nonadjacent_middle_cores :=
        tube_disjoint_nonadjacent_middle_cores
      tube_disjoint_nonadjacent_tubes :=
        tube_disjoint_nonadjacent_tubes
      normal_eq_positive_quarter_turn := by
        intro j hj
        rfl }
  refine ⟨
    { orientedTubes := orientedTubes
      initial_halfWidth_lt_cone_mul_lowerParam := by
        intro j hj
        simpa [orientedTubes] using halfWidth_lt_initialCone_mul_lowerParam j hj
      terminal_halfWidth_lt_cone_mul_one_sub_upperParam := by
        intro j hj
        simpa [orientedTubes] using
          halfWidth_lt_terminalCone_mul_one_sub_upperParam j hj
      initial_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hprev
        simpa [orientedTubes] using
          initial_halfWidth_mul_normal_norm_lt_away_quarter j hj hprev
      terminal_halfWidth_mul_normal_norm_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          terminal_halfWidth_mul_normal_norm_lt_away_quarter j hj hnext
      successive_halfWidth_normal_sum_lt_away_quarter := by
        intro j hj hnext
        simpa [orientedTubes] using
          successive_halfWidth_normal_sum_lt_away_quarter j hj hnext }⟩

