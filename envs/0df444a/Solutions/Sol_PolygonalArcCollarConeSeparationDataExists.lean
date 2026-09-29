-- Prove2me | solution 1 for PolygonalArcCollarConeSeparationDataExists
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T02:57:13.561246+00:00
-- url     : https://prove2.me/submissions/6abe4633-ecfa-4170-b2ab-4c34920dab7e

import Definitions.Def_PolygonalArcCollarConeSeparationData
import Theorems.Thm_PolygonalArcAdjacentOutwardDirectionsNotSameRay
import Theorems.Thm_PlanarRot90ConeAvoidsRay
import Theorems.Thm_PlanarRot90SameSideConesDisjoint
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Order

open Classical
noncomputable section

set_option maxHeartbeats 3000000

-- [TABLET NODE: PolygonalArcCollarConeSeparationDataExists]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists,
-- cone-bound and signed-cone separation phase.
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L29-L109, L1190-L1461
theorem solution (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarConeSeparationData γ controlRadii middleSegments
        forbiddenMargins) := by
  have segmentEndpoints_ne :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        γ.vertices[j] ≠ γ.vertices[j + 1] := by
    intro j hj
    have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft :=
        controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
      nlinarith
    exact dist_pos.mp hdist_pos
  have forwardDirection_ne_zero :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        γ.vertices[j + 1] - γ.vertices[j] ≠ 0 := by
    intro j hj
    exact sub_ne_zero.mpr (segmentEndpoints_ne j hj).symm
  have backwardDirection_ne_zero :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        γ.vertices[j] - γ.vertices[j + 1] ≠ 0 := by
    intro j hj
    exact sub_ne_zero.mpr (segmentEndpoints_ne j hj)
  have initialConeAvoidsPreviousRay :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∃ κ : ℝ, 0 < κ ∧
          ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
            c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
              t • (γ.vertices[j + 1] - γ.vertices[j]) +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    intro j hj hprev
    exact
      PlanarRot90ConeAvoidsRay
        (d := γ.vertices[j + 1] - γ.vertices[j])
        (v := γ.vertices[j - 1] - γ.vertices[j])
        (forwardDirection_ne_zero j hj)
        (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ hprev hj).1
  have terminalConeAvoidsNextRay :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ κ : ℝ, 0 < κ ∧
            ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 → |s| < κ * t →
              c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
                t • (γ.vertices[j] - γ.vertices[j + 1]) +
                  s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
    intro j hj hnext
    have hnot :
        ¬ ∃ a : ℝ, 0 < a ∧
          γ.vertices[j + 2] - γ.vertices[j + 1] =
            a • (γ.vertices[j] - γ.vertices[j + 1]) := by
      simpa [Nat.add_assoc] using
        (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ
          (i := j + 1) (Nat.succ_pos j) hnext).2
    exact
      PlanarRot90ConeAvoidsRay
        (d := γ.vertices[j] - γ.vertices[j + 1])
        (v := γ.vertices[j + 2] - γ.vertices[j + 1])
        (backwardDirection_ne_zero j hj) hnot
  have successiveOutwardConesDisjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ κ : ℝ, 0 < κ ∧
            ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
              |b| < κ * a → |r| < κ * c →
                a • (γ.vertices[j] - γ.vertices[j + 1]) +
                    b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
                  c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
                    r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    intro j hj hnext
    have hnot :
        ¬ ∃ A : ℝ, 0 < A ∧
          γ.vertices[j + 2] - γ.vertices[j + 1] =
            A • (γ.vertices[j] - γ.vertices[j + 1]) := by
      simpa [Nat.add_assoc] using
        (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ
          (i := j + 1) (Nat.succ_pos j) hnext).2
    exact
      PlanarRot90SameSideConesDisjoint
        (u := γ.vertices[j] - γ.vertices[j + 1])
        (d := γ.vertices[j + 2] - γ.vertices[j + 1])
        (backwardDirection_ne_zero j hj)
        (forwardDirection_ne_zero (j + 1) hnext) hnot

  let normal : (j : ℕ) → j + 1 < γ.vertices.length →
      EuclideanSpace ℝ (Fin 2) := fun j hj =>
    PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j])
  let initialRayCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      Classical.choose (initialConeAvoidsPreviousRay j hj hprev)
    else
      1
  let terminalRayCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      Classical.choose (terminalConeAvoidsNextRay j hj hnext)
    else
      1
  let initialPairCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hprev : 0 < j then
      Classical.choose
        (successiveOutwardConesDisjoint (j - 1)
          (by
            have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
          (by
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))
    else
      1
  let terminalPairCone : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    if hnext : (j + 1) + 1 < γ.vertices.length then
      Classical.choose (successiveOutwardConesDisjoint j hj hnext)
    else
      1
  let initialConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (initialRayCone j hj) (initialPairCone j hj)
  let terminalConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (terminalRayCone j hj) (terminalPairCone j hj)

  have initialRayCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialRayCone j hj := by
    intro j hj
    dsimp [initialRayCone]
    by_cases hprev : 0 < j
    · simpa [hprev] using
        (Classical.choose_spec (initialConeAvoidsPreviousRay j hj hprev)).1
    · simp [hprev]
  have terminalRayCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalRayCone j hj := by
    intro j hj
    dsimp [terminalRayCone]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · simpa [hnext] using
        (Classical.choose_spec (terminalConeAvoidsNextRay j hj hnext)).1
    · simp [hnext]
  have initialPairCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialPairCone j hj := by
    intro j hj
    dsimp [initialPairCone]
    by_cases hprev : 0 < j
    · simpa [hprev] using
        (Classical.choose_spec
          (successiveOutwardConesDisjoint (j - 1)
            (by
              have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj')
            (by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj))).1
    · simp [hprev]
  have terminalPairCone_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalPairCone j hj := by
    intro j hj
    dsimp [terminalPairCone]
    by_cases hnext : (j + 1) + 1 < γ.vertices.length
    · simpa [hnext] using
        (Classical.choose_spec (successiveOutwardConesDisjoint j hj hnext)).1
    · simp [hnext]
  have initialConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialConeBound j hj := by
    intro j hj
    dsimp [initialConeBound]
    exact lt_min (initialRayCone_pos j hj) (initialPairCone_pos j hj)
  have terminalConeBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalConeBound j hj := by
    intro j hj
    dsimp [terminalConeBound]
    exact lt_min (terminalRayCone_pos j hj) (terminalPairCone_pos j hj)

  have lineMap_sub_left :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (t : ℝ),
        AffineMap.lineMap A B t - A = t • (B - A) := by
    intro A B t
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module]
    ring
  have lineMap_sub_right :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (t : ℝ),
        AffineMap.lineMap A B t - B = (1 - t) • (A - B) := by
    intro A B t
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module]
    ring
  have lineMap_add_sub_left :
      ∀ (A B n : EuclideanSpace ℝ (Fin 2)) (t s : ℝ),
        AffineMap.lineMap A B t + s • n - A = t • (B - A) + s • n := by
    intro A B n t s
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module, sub_eq_add_neg]
    ring
  have lineMap_add_sub_right :
      ∀ (A B n : EuclideanSpace ℝ (Fin 2)) (t s : ℝ),
        AffineMap.lineMap A B t + s • n - B = (1 - t) • (A - B) + s • n := by
    intro A B n t s
    apply PiLp.ext
    intro k
    simp [AffineMap.lineMap_apply_module, sub_eq_add_neg]
    ring
  have PlanarRot90_neg :
      ∀ v : EuclideanSpace ℝ (Fin 2), PlanarRot90 (-v) = -PlanarRot90 v := by
    intro v
    apply PiLp.ext
    intro k
    fin_cases k <;> simp [PlanarRot90]
  have initialConeAvoidsPreviousRay_bound :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 →
          |s| < initialConeBound j hj * t →
            c • (γ.vertices[j - 1] - γ.vertices[j]) ≠
              t • (γ.vertices[j + 1] - γ.vertices[j]) +
                s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    intro j hj hprev c t s hc ht hs_ne hs_lt
    have hle :
        initialConeBound j hj ≤
          Classical.choose (initialConeAvoidsPreviousRay j hj hprev) := by
      dsimp [initialConeBound, initialRayCone]
      exact le_trans (min_le_left _ _) (by simp [hprev])
    have hs_lt' :
        |s| < Classical.choose (initialConeAvoidsPreviousRay j hj hprev) * t :=
      lt_of_lt_of_le hs_lt (mul_le_mul_of_nonneg_right hle (le_of_lt ht))
    exact
      (Classical.choose_spec (initialConeAvoidsPreviousRay j hj hprev)).2
        c t s hc ht hs_ne hs_lt'
  have terminalConeAvoidsNextRay_bound :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ c t s : ℝ, 0 ≤ c → 0 < t → s ≠ 0 →
            |s| < terminalConeBound j hj * t →
              c • (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
                t • (γ.vertices[j] - γ.vertices[j + 1]) +
                  s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
    intro j hj hnext c t s hc ht hs_ne hs_lt
    have hle :
        terminalConeBound j hj ≤
          Classical.choose (terminalConeAvoidsNextRay j hj hnext) := by
      dsimp [terminalConeBound, terminalRayCone]
      exact le_trans (min_le_left _ _) (by simp [hnext])
    have hs_lt' :
        |s| < Classical.choose (terminalConeAvoidsNextRay j hj hnext) * t :=
      lt_of_lt_of_le hs_lt (mul_le_mul_of_nonneg_right hle (le_of_lt ht))
    exact
      (Classical.choose_spec (terminalConeAvoidsNextRay j hj hnext)).2
        c t s hc ht hs_ne hs_lt'
  have successiveOutwardConesDisjoint_bound :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
            |b| < terminalConeBound j hj * a →
              |r| < initialConeBound (j + 1) hnext * c →
                a • (γ.vertices[j] - γ.vertices[j + 1]) +
                    b • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) ≠
                  c • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
                    r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
    intro j hj hnext a c b r ha hc hbr hb hr
    have hleT :
        terminalConeBound j hj ≤
          Classical.choose (successiveOutwardConesDisjoint j hj hnext) := by
      dsimp [terminalConeBound, terminalPairCone]
      exact le_trans (min_le_right _ _) (by simp [hnext])
    have hleI :
        initialConeBound (j + 1) hnext ≤
          Classical.choose (successiveOutwardConesDisjoint j hj hnext) := by
      dsimp [initialConeBound, initialPairCone]
      refine le_trans (min_le_right _ _) ?_
      simp
    have hb' :
        |b| < Classical.choose (successiveOutwardConesDisjoint j hj hnext) * a :=
      lt_of_lt_of_le hb (mul_le_mul_of_nonneg_right hleT (le_of_lt ha))
    have hr' :
        |r| < Classical.choose (successiveOutwardConesDisjoint j hj hnext) * c :=
      lt_of_lt_of_le hr (mul_le_mul_of_nonneg_right hleI (le_of_lt hc))
    exact
      (Classical.choose_spec (successiveOutwardConesDisjoint j hj hnext)).2
        a c b r ha hc hbr hb' hr'
  have initial_signed_cone_disjoint_previous_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s ≠ 0 ∧ |s| < initialConeBound j hj * t ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • normal j hj}
          (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
    intro j hj hprev
    rw [Set.disjoint_left]
    intro z hzCone hzSeg
    rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
    rw [segment_eq_image_lineMap] at hzSeg
    rcases hzSeg with ⟨u, hu, hzPrev⟩
    have hPrevVec :
        z - γ.vertices[j] =
          (1 - u) • (γ.vertices[j - 1] - γ.vertices[j]) := by
      rw [← hzPrev]
      exact lineMap_sub_right γ.vertices[j - 1] γ.vertices[j] u
    have hConeVec :
        z - γ.vertices[j] =
          t • (γ.vertices[j + 1] - γ.vertices[j]) +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
      rw [hz]
      exact lineMap_add_sub_left γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have heq :
        (1 - u) • (γ.vertices[j - 1] - γ.vertices[j]) =
          t • (γ.vertices[j + 1] - γ.vertices[j]) +
            s • PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
      exact hPrevVec.symm.trans hConeVec
    exact
      initialConeAvoidsPreviousRay_bound j hj hprev (1 - u) t s
        (by nlinarith [hu.2]) ht.1 hs_ne hs_lt heq
  have terminal_signed_cone_disjoint_next_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s ≠ 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
                z =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                    s • normal j hj}
            (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro z hzCone hzSeg
    rcases hzCone with ⟨t, ht, s, hs_ne, hs_lt, hz⟩
    rw [segment_eq_image_lineMap] at hzSeg
    rcases hzSeg with ⟨u, hu, hzNext⟩
    have hNextVec :
        z - γ.vertices[j + 1] =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      rw [← hzNext]
      exact lineMap_sub_left γ.vertices[j + 1] γ.vertices[j + 2] u
    have hConeVec :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            s • normal j hj := by
      rw [hz]
      exact lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have hrot :
        (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          s • normal j hj := by
      have hback : γ.vertices[j] - γ.vertices[j + 1] =
          -(γ.vertices[j + 1] - γ.vertices[j]) := by
        abel
      rw [hback, PlanarRot90_neg]
      simp [normal]
    have heq :
        u • (γ.vertices[j + 2] - γ.vertices[j + 1]) =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) := by
      have hConeVec' :
          z - γ.vertices[j + 1] =
            (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
              (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
        hConeVec.trans (by rw [hrot])
      exact hNextVec.symm.trans hConeVec'
    exact
      terminalConeAvoidsNextRay_bound j hj hnext u (1 - t) (-s)
        hu.1 (by nlinarith [ht.2]) (by simpa using neg_ne_zero.mpr hs_ne)
        (by simpa [abs_neg] using hs_lt) heq
  have successive_positive_negative_cones_disjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, 0 < s ∧ s < terminalConeBound j hj * (1 - t) ∧
                z =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                    s • normal j hj}
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s < 0 ∧ |s| < initialConeBound (j + 1) hnext * t ∧
                z =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                    s • normal (j + 1) hnext} := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro z hzL hzR
    rcases hzL with ⟨t, ht, s, hs_pos, hs_lt, hzL⟩
    rcases hzR with ⟨u, hu, r, hr_neg, hr_lt, hzR⟩
    have hLeftVec :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) + s • normal j hj := by
      rw [hzL]
      exact lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have hRightVec :
        z - γ.vertices[j + 1] =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      rw [hzR]
      exact lineMap_add_sub_left γ.vertices[j + 1] γ.vertices[j + 2]
        (normal (j + 1) hnext) u r
    have hrot :
        (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          s • normal j hj := by
      have hback : γ.vertices[j] - γ.vertices[j + 1] =
          -(γ.vertices[j + 1] - γ.vertices[j]) := by
        abel
      rw [hback, PlanarRot90_neg]
      simp [normal]
    have heq :
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      have hLeftVec' :
          z - γ.vertices[j + 1] =
            (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
              (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
        hLeftVec.trans (by rw [hrot])
      exact hLeftVec'.symm.trans hRightVec
    exact
      successiveOutwardConesDisjoint_bound j hj hnext (1 - t) u (-s) r
        (by nlinarith [ht.2]) hu.1 (by nlinarith [hs_pos, hr_neg])
        (by simpa [abs_neg, abs_of_pos hs_pos] using hs_lt)
        hr_lt heq
  have successive_negative_positive_cones_disjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s < 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
                z =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                    s • normal j hj}
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, 0 < s ∧ s < initialConeBound (j + 1) hnext * t ∧
                z =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                    s • normal (j + 1) hnext} := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro z hzL hzR
    rcases hzL with ⟨t, ht, s, hs_neg, hs_lt, hzL⟩
    rcases hzR with ⟨u, hu, r, hr_pos, hr_lt, hzR⟩
    have hLeftVec :
        z - γ.vertices[j + 1] =
          (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) + s • normal j hj := by
      rw [hzL]
      exact lineMap_add_sub_right γ.vertices[j] γ.vertices[j + 1]
        (normal j hj) t s
    have hRightVec :
        z - γ.vertices[j + 1] =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      rw [hzR]
      exact lineMap_add_sub_left γ.vertices[j + 1] γ.vertices[j + 2]
        (normal (j + 1) hnext) u r
    have hrot :
        (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          s • normal j hj := by
      have hback : γ.vertices[j] - γ.vertices[j + 1] =
          -(γ.vertices[j + 1] - γ.vertices[j]) := by
        abel
      rw [hback, PlanarRot90_neg]
      simp [normal]
    have heq :
        (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
            (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) =
          u • (γ.vertices[j + 2] - γ.vertices[j + 1]) +
            r • PlanarRot90 (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
      have hLeftVec' :
          z - γ.vertices[j + 1] =
            (1 - t) • (γ.vertices[j] - γ.vertices[j + 1]) +
              (-s) • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]) :=
        hLeftVec.trans (by rw [hrot])
      exact hLeftVec'.symm.trans hRightVec
    exact
      successiveOutwardConesDisjoint_bound j hj hnext (1 - t) u (-s) r
        (by nlinarith [ht.2]) hu.1 (by nlinarith [hs_neg, hr_pos])
        (by simpa [abs_neg] using hs_lt)
        (by simpa [abs_of_pos hr_pos] using hr_lt) heq
  refine ⟨{
    initialConeBound := initialConeBound
    terminalConeBound := terminalConeBound
    initialConeBound_pos := initialConeBound_pos
    terminalConeBound_pos := terminalConeBound_pos
    initial_signed_cone_disjoint_previous_segment := by
      intro j hj hprev
      simpa [normal] using
        (initial_signed_cone_disjoint_previous_segment j hj hprev)
    terminal_signed_cone_disjoint_next_segment := by
      intro j hj hnext
      simpa [normal] using
        (terminal_signed_cone_disjoint_next_segment j hj hnext)
    successive_positive_negative_cones_disjoint := by
      intro j hj hnext
      simpa [normal] using
        (successive_positive_negative_cones_disjoint j hj hnext)
    successive_negative_positive_cones_disjoint := by
      intro j hj hnext
      simpa [normal] using
        (successive_negative_positive_cones_disjoint j hj hnext) }⟩
