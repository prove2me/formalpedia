-- Prove2me | solution 2 for RawBlending.UB.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:43:37.169108+00:00
-- url     : https://prove2.me/submissions/d5362181-cf38-446b-b81c-eb5f27de519b

import Mathlib
import Definitions.Def_RawBlending_UB_Policy

open RawBlending.UB

private def d0 : Data where
  T := 1
  a1 := 1
  a2 := 2
  e := fun _ => 0
  σ := fun _ => 1
  h1 := fun _ => 0
  h2 := fun _ => 1
  c1 := fun _ => 1
  c2 := fun _ => 1
  DR := fun _ => ⟨{(0, 0)}, fun _ => 1⟩
  qq1 := fun _ => ⟨{0}, fun _ => 1⟩
  qq2 := fun _ => ⟨{0}, fun _ => 1⟩

private lemma d0_standing : d0.Standing := by
  refine ⟨by norm_num [d0], by norm_num [d0], by norm_num [d0], ?_, ?_⟩
  · intro t _ _
    refine ⟨by norm_num [d0], by norm_num [d0], by norm_num [d0], by norm_num [d0],
      by norm_num [d0], by norm_num [d0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun _ _ => by norm_num [d0], by simp [d0]⟩
    · intro z hz
      simp [d0] at hz
      rw [hz]
      norm_num
    · exact ⟨fun _ _ => by norm_num [d0], by simp [d0]⟩
    · exact ⟨fun _ _ => by norm_num [d0], by simp [d0]⟩
    · intro q hq
      simp [d0] at hq
      rw [hq]
    · intro q hq
      simp [d0] at hq
      rw [hq]
  · intro t _ _
    norm_num [d0]

private lemma J_d0_eq (w : Vec) : J d0 1 w = w.1 + 3 * w.2 := by
  have hV : V d0 (1 + 1) w = boundary d0 w := by
    change Vtg d0 (d0.T + 1 - (1 + 1)) w = boundary d0 w
    have h0 : d0.T + 1 - (1 + 1) = 0 := by norm_num [d0]
    rw [h0]
    rfl
  unfold J Jstep
  rw [hV]
  simp only [boundary, p, d0]
  ring

theorem solution :
    ¬ (∀ (d : Data) (_hd : d.Standing) (t : ℕ)
        (_ht : 1 ≤ t) (_htT : t ≤ d.T),
        ∃ C : Curves, IsUBCurves (J d t) d.a1 d.a2 C ∧
          ∀ D R : ℝ, 0 ≤ D → 0 ≤ R →
            RegionsCover C d.a1 d.a2 D R ∧
            (d.a1 * R < D → RegionsDisjoint C d.a1 d.a2 D R) ∧
            ∀ y : Vec, y ∈ orthant →
              Minimizes (J d t) (E2 d.a1 d.a2 y D R)
                (ubAction C d.a1 d.a2 D R y)) := by
  intro h
  obtain ⟨C, hUB, hDR⟩ := h d0 d0_standing 1 le_rfl (by norm_num [d0])
  have hmin_wbar : Minimizes (J d0 1) orthant C.wbar := hUB.2.2.2.2.2.2.2.1
  have hmin_alpha : ∀ x : ℝ, 0 ≤ x →
      Minimizes (J d0 1) {w : Vec | w ∈ orthant ∧ d0.a1 * w.1 + d0.a2 * w.2 = x} (C.α x) :=
    hUB.2.2.2.2.2.2.2.2.2.2.1
  have hmin_beta : ∀ x : ℝ, 0 ≤ x →
      Minimizes (J d0 1) {w : Vec | w ∈ orthant ∧ w.1 + w.2 = x} (C.β x) :=
    hUB.2.2.2.2.2.2.2.2.2.2.2
  -- Determine C.wbar = (0, 0)
  have hwbar0 : C.wbar.1 = 0 ∧ C.wbar.2 = 0 := by
    have hw_orth : (0 : ℝ) ≤ C.wbar.1 ∧ (0 : ℝ) ≤ C.wbar.2 := hmin_wbar.1
    have hle := hmin_wbar.2 (0, 0) ⟨le_rfl, le_rfl⟩
    rw [J_d0_eq, J_d0_eq] at hle
    exact ⟨by linarith, by linarith⟩
  -- Determine (C.α 2).1 = 2
  have halpha2 : (C.α 2).1 = 2 := by
    have hm := hmin_alpha 2 (by norm_num)
    have hfeas : ((2 : ℝ), (0 : ℝ)) ∈
        {w : Vec | w ∈ orthant ∧ d0.a1 * w.1 + d0.a2 * w.2 = 2} :=
      ⟨⟨by norm_num, by norm_num⟩, by norm_num [d0]⟩
    have hle := hm.2 (2, 0) hfeas
    rw [J_d0_eq, J_d0_eq] at hle
    have h_orth : (0 : ℝ) ≤ (C.α 2).1 ∧ (0 : ℝ) ≤ (C.α 2).2 := hm.1.1
    have heq : (1 : ℝ) * (C.α 2).1 + 2 * (C.α 2).2 = 2 := hm.1.2
    linarith
  -- Determine (C.β 3).1 = 3
  have hbeta3 : (C.β 3).1 = 3 := by
    have hm := hmin_beta 3 (by norm_num)
    have hfeas : ((3 : ℝ), (0 : ℝ)) ∈
        {w : Vec | w ∈ orthant ∧ w.1 + w.2 = 3} :=
      ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    have hle := hm.2 (3, 0) hfeas
    rw [J_d0_eq, J_d0_eq] at hle
    have h_orth : (0 : ℝ) ≤ (C.β 3).1 ∧ (0 : ℝ) ≤ (C.β 3).2 := hm.1.1
    have heq : (C.β 3).1 + (C.β 3).2 = 3 := hm.1.2
    linarith
  -- Specialize to D = 4, R = 1, where a1 * R = 1 < 4 = D and a2 * R = 2 ≤ 4 = D
  have hdisj : RegionsDisjoint C d0.a1 d0.a2 4 1 :=
    (hDR 4 1 (by norm_num) (by norm_num)).2.1 (by norm_num [d0])
  have hL1 : L1 d0.a1 d0.a2 4 1 = 0 := by
    simp [L1, d0]
    norm_num
  have hL2 : L2 d0.a1 d0.a2 4 1 = 1 := by
    simp [L2, K2, d0]
    norm_num
  -- Strictly interior inventory point y = (2, 2) lies in R1a ∩ R3c
  let y : Vec := (2, 2)
  have hy_orth : y ∈ orthant := ⟨by norm_num, by norm_num⟩
  have hy_not_R0 : y ∉ R0 C d0.a1 d0.a2 4 1 := by
    intro hR0
    rcases hR0.2.1 with h1 | h2
    · rw [hwbar0.1, hL1] at h1; norm_num [y] at h1
    · rw [hwbar0.2, hL2] at h2; norm_num [y] at h2
  have hy_dem : exceedsDemand C d0.a1 d0.a2 4 y := by
    simp only [exceedsDemand, hwbar0.1, hwbar0.2, d0, y]
    norm_num
  have hy_cap : exceedsCapacity C 1 y := by
    simp only [exceedsCapacity, hwbar0.1, hwbar0.2, y]
    norm_num
  have hy_R1 : y ∈ region C d0.a1 d0.a2 4 1 ⟨1, by omega⟩ := by
    apply Or.inl
    refine ⟨hy_orth, hy_not_R0, ?_, hy_dem⟩
    have h2 : d0.a1 * y.1 + d0.a2 * y.2 - 4 = 2 := by norm_num [d0, y]
    rw [h2, halpha2]
  have hy_R3 : y ∈ region C d0.a1 d0.a2 4 1 ⟨3, by omega⟩ := by
    apply Or.inr
    refine ⟨hy_orth, hy_not_R0, hy_dem, hy_cap, ?_, ?_⟩
    · have h2 : d0.a1 * y.1 + d0.a2 * y.2 - 4 = 2 := by norm_num [d0, y]
      rw [h2, halpha2, hL1]
      norm_num [y]
    · have h3 : y.1 + y.2 - 1 = 3 := by norm_num [y]
      rw [h3, hbeta3, hL1]
      norm_num [y]
  have h13 : (⟨1, by omega⟩ : Fin 6) ≠ ⟨3, by omega⟩ := by decide
  exact Set.disjoint_left.mp (hdisj ⟨1, by omega⟩ ⟨3, by omega⟩ h13) hy_R1 hy_R3
