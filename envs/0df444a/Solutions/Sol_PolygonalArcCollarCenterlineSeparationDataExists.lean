-- Prove2me | solution 1 for PolygonalArcCollarCenterlineSeparationDataExists
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-28T02:35:11.703144+00:00
-- url     : https://prove2.me/submissions/12442f15-9e49-4fc0-a678-2ab420619ffd

import Definitions.Def_PolygonalArcCollarCenterlineSeparationData
import Theorems.Thm_PositiveSeparation
import Mathlib.Tactic.Linarith.Frontend

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarCenterlineSeparationDataExists]
-- Source phase: PolygonalArcCollarCompatibleOrientedTubeDataExists,
-- compact centerline/PositiveSeparation phase.
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarCompatibleOrientedTubeDataExists.lean#L332-L614
 theorem solution (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (parameters :
      PolygonalArcCollarParameterData γ controlRadii middleSegments forbiddenMargins) :
    Nonempty
      (PolygonalArcCollarCenterlineSeparationData γ controlRadii middleSegments
        forbiddenMargins parameters) := by
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
  let initialCenterline : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
      Set.Icc (parameters.leftParam j hj) (1 : ℝ)
  let terminalCenterline : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
      Set.Icc (0 : ℝ) (parameters.rightParam j hj)
  have segment_nonempty :
      ∀ (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (segment ℝ γ.vertices[k] γ.vertices[k + 1]).Nonempty := by
    intro k hk
    exact ⟨γ.vertices[k], by simp [left_mem_segment]⟩
  have segment_compact :
      ∀ (k : ℕ) (hk : k + 1 < γ.vertices.length),
        IsCompact (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
    intro k hk
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have initialCenterline_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (initialCenterline j hj).Nonempty := by
    intro j hj
    refine ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
      (parameters.leftParam j hj), ?_⟩
    exact ⟨parameters.leftParam j hj,
      ⟨le_rfl, le_of_lt
        ((parameters.leftParam_lt_rightParam j hj).trans
          (parameters.rightParam_lt_one j hj))⟩,
      rfl⟩
  have terminalCenterline_nonempty :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (terminalCenterline j hj).Nonempty := by
    intro j hj
    refine ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] (0 : ℝ), ?_⟩
    exact ⟨0, ⟨le_rfl,
      le_of_lt ((parameters.leftParam_pos j hj).trans
        (parameters.leftParam_lt_rightParam j hj))⟩, rfl⟩
  have initialCenterline_compact :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        IsCompact (initialCenterline j hj) := by
    intro j hj
    dsimp [initialCenterline]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have terminalCenterline_compact :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        IsCompact (terminalCenterline j hj) := by
    intro j hj
    dsimp [terminalCenterline]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have initialCenterline_disjoint_previous :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        Disjoint (initialCenterline j hj)
          (segment ℝ γ.vertices[j - 1] γ.vertices[j]) := by
    intro j hj hprev
    rw [Set.disjoint_left]
    intro x hxA hxPrev
    rcases hxA with ⟨t, ht, rfl⟩
    have hCurrent :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨le_trans (le_of_lt (parameters.leftParam_pos j hj)) ht.1,
        ht.2⟩, rfl⟩
    have hprevSeg : (j - 1) + 1 < γ.vertices.length := by
      have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj'
    have hlt : j - 1 < j := Nat.sub_lt hprev Nat.zero_lt_one
    have hinter :
        segment ℝ γ.vertices[j - 1] γ.vertices[j] ∩
            segment ℝ γ.vertices[j] γ.vertices[j + 1] =
          ({γ.vertices[j]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw := γ.segment_intersections (i := j - 1) (j := j) hprevSeg hj hlt
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hraw
    have hxVertex :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t = γ.vertices[j] := by
      have hxInter :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
            segment ℝ γ.vertices[j - 1] γ.vertices[j] ∩
              segment ℝ γ.vertices[j] γ.vertices[j + 1] :=
        ⟨hxPrev, hCurrent⟩
      rw [hinter] at hxInter
      simpa using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (segmentEndpoints_ne j hj)
    have ht0 : t = 0 := hf (by simpa [f] using hxVertex)
    linarith [parameters.leftParam_pos j hj, ht.1]
  have terminalCenterline_disjoint_next :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint (terminalCenterline j hj)
            (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]) := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro x hxA hxNext
    rcases hxA with ⟨t, ht, rfl⟩
    have hCurrent :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨ht.1, le_trans ht.2
        (le_of_lt (parameters.rightParam_lt_one j hj))⟩, rfl⟩
    have hinter :
        segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] =
          ({γ.vertices[j + 1]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw :=
        γ.segment_intersections (i := j) (j := j + 1) hj hnext
          (Nat.lt_succ_self j)
      simpa using hraw
    have hxVertex :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t =
          γ.vertices[j + 1] := by
      have hxInter :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
            segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
              segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] :=
        ⟨hCurrent, hxNext⟩
      rw [hinter] at hxInter
      simpa using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (segmentEndpoints_ne j hj)
    have ht1 : t = 1 := hf (by simpa [f] using hxVertex)
    linarith [parameters.rightParam_lt_one j hj, ht.2]
  have successiveCenterlines_disjoint :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          Disjoint (terminalCenterline j hj) (initialCenterline (j + 1) hnext) := by
    intro j hj hnext
    rw [Set.disjoint_left]
    intro x hxA hxB
    rcases hxA with ⟨t, ht, rfl⟩
    rcases hxB with ⟨u, hu, hxu⟩
    have hCurrent :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨ht.1, le_trans ht.2
        (le_of_lt (parameters.rightParam_lt_one j hj))⟩, rfl⟩
    have hNext :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
          segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] := by
      rw [← hxu, segment_eq_image_lineMap]
      exact ⟨u, ⟨le_trans
        (le_of_lt (parameters.leftParam_pos (j + 1) hnext)) hu.1,
        hu.2⟩, rfl⟩
    have hinter :
        segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
            segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] =
          ({γ.vertices[j + 1]} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hraw :=
        γ.segment_intersections (i := j) (j := j + 1) hj hnext
          (Nat.lt_succ_self j)
      simpa using hraw
    have hxVertex :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t =
          γ.vertices[j + 1] := by
      have hxInter :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
            segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
              segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] :=
        ⟨hCurrent, hNext⟩
      rw [hinter] at hxInter
      simpa using hxInter
    let f : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
    have hf : Function.Injective f :=
      AffineMap.lineMap_injective (k := ℝ) (segmentEndpoints_ne j hj)
    have ht1 : t = 1 := hf (by simpa [f] using hxVertex)
    linarith [parameters.rightParam_lt_one j hj, ht.2]
  have initialAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, t ∈ Set.Icc (parameters.leftParam j hj) (1 : ℝ) →
            ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
              δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hprev
    let A : Set (EuclideanSpace ℝ (Fin 2)) := initialCenterline j hj
    let B : Set (EuclideanSpace ℝ (Fin 2)) :=
      segment ℝ γ.vertices[j - 1] γ.vertices[j]
    have hprevSeg : (j - 1) + 1 < γ.vertices.length := by
      have hj' : j < γ.vertices.length := Nat.lt_of_succ_lt hj
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using hj'
    have hAne : A.Nonempty := by
      simpa [A] using initialCenterline_nonempty j hj
    have hBne : B.Nonempty := by
      simpa [B, Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using
        segment_nonempty (j - 1) hprevSeg
    have hAc : IsCompact A := by
      simpa [A] using initialCenterline_compact j hj
    have hBc : IsCompact B := by
      simpa [B, Nat.sub_add_cancel (Nat.succ_le_of_lt hprev)] using
        segment_compact (j - 1) hprevSeg
    have hdisj : Disjoint A B := by
      simpa [A, B] using initialCenterline_disjoint_previous j hj hprev
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
    refine ⟨δ, hδpos, ?_⟩
    intro t ht q hq
    exact hδ (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
      (by exact ⟨t, ht, rfl⟩) q (by simpa [B] using hq)
  have terminalAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (parameters.rightParam j hj) →
              ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
                δ ≤ dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q := by
    intro j hj hnext
    let A : Set (EuclideanSpace ℝ (Fin 2)) := terminalCenterline j hj
    let B : Set (EuclideanSpace ℝ (Fin 2)) :=
      segment ℝ γ.vertices[j + 1] γ.vertices[j + 2]
    have hAne : A.Nonempty := by
      simpa [A] using terminalCenterline_nonempty j hj
    have hBne : B.Nonempty := by
      simpa [B] using segment_nonempty (j + 1) hnext
    have hAc : IsCompact A := by
      simpa [A] using terminalCenterline_compact j hj
    have hBc : IsCompact B := by
      simpa [B] using segment_compact (j + 1) hnext
    have hdisj : Disjoint A B := by
      simpa [A, B] using terminalCenterline_disjoint_next j hj hnext
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
    refine ⟨δ, hδpos, ?_⟩
    intro t ht q hq
    exact hδ (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
      (by exact ⟨t, ht, rfl⟩) q (by simpa [B] using hq)
  have successiveAwayExists :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (parameters.rightParam j hj) →
              ∀ u : ℝ, u ∈ Set.Icc
                (parameters.leftParam (j + 1) hnext) (1 : ℝ) →
                δ ≤
                  dist
                    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u) := by
    intro j hj hnext
    let A : Set (EuclideanSpace ℝ (Fin 2)) := terminalCenterline j hj
    let B : Set (EuclideanSpace ℝ (Fin 2)) := initialCenterline (j + 1) hnext
    have hAne : A.Nonempty := by
      simpa [A] using terminalCenterline_nonempty j hj
    have hBne : B.Nonempty := by
      simpa [B] using initialCenterline_nonempty (j + 1) hnext
    have hAc : IsCompact A := by
      simpa [A] using terminalCenterline_compact j hj
    have hBc : IsCompact B := by
      simpa [B] using initialCenterline_compact (j + 1) hnext
    have hdisj : Disjoint A B := by
      simpa [A, B] using successiveCenterlines_disjoint j hj hnext
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (A := A) (B := B) hAne hBne hAc hBc hdisj
    refine ⟨δ, hδpos, ?_⟩
    intro t ht u hu
    exact hδ (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
      (by exact ⟨t, ht, rfl⟩)
      (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u)
      (by exact ⟨u, hu, rfl⟩)
  let initialAwaySeparation :
      (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ :=
    fun j hj hprev => Classical.choose (initialAwayExists j hj hprev)
  let terminalAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => Classical.choose (terminalAwayExists j hj hnext)
  let successiveAwaySeparation :
      ∀ (j : ℕ), (hj : j + 1 < γ.vertices.length) →
        (j + 1) + 1 < γ.vertices.length → ℝ :=
    fun j hj hnext => Classical.choose (successiveAwayExists j hj hnext)
  have initialAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
        0 < initialAwaySeparation j hj hprev := by
    intro j hj hprev
    simpa [initialAwaySeparation] using
      (Classical.choose_spec (initialAwayExists j hj hprev)).1
  have terminalAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < terminalAwaySeparation j hj hnext := by
    intro j hj hnext
    simpa [terminalAwaySeparation] using
      (Classical.choose_spec (terminalAwayExists j hj hnext)).1
  have successiveAwaySeparation_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (hnext : (j + 1) + 1 < γ.vertices.length),
          0 < successiveAwaySeparation j hj hnext := by
    intro j hj hnext
    simpa [successiveAwaySeparation] using
      (Classical.choose_spec (successiveAwayExists j hj hnext)).1
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
    exact
      (Classical.choose_spec (initialAwayExists j hj hprev)).2 t
        (by simpa [parameters.leftParam_eq j hj] using ht) q hq
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
    exact
      (Classical.choose_spec (terminalAwayExists j hj hnext)).2 t
        (by simpa [parameters.rightParam_eq j hj] using ht) q hq
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
    exact
      (Classical.choose_spec (successiveAwayExists j hj hnext)).2 t
        (by simpa [parameters.rightParam_eq j hj] using ht) u
        (by simpa [parameters.leftParam_eq (j + 1) hnext] using hu)
  exact ⟨
    { initialAwaySeparation := initialAwaySeparation
      terminalAwaySeparation := terminalAwaySeparation
      successiveAwaySeparation := successiveAwaySeparation
      initialAwaySeparation_pos := initialAwaySeparation_pos
      terminalAwaySeparation_pos := terminalAwaySeparation_pos
      successiveAwaySeparation_pos := successiveAwaySeparation_pos
      initial_centerline_previous_segment_away :=
        initial_centerline_previous_segment_away
      terminal_centerline_next_segment_away :=
        terminal_centerline_next_segment_away
      successive_centerlines_away := successive_centerlines_away }⟩
