-- Prove2me | solution 1 for RawBlending.UB.theorem_1_production
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:12:44.22538+00:00
-- url     : https://prove2.me/submissions/65dfdd71-35e4-4823-97e1-85b33674ed2f

import Mathlib
import Definitions.Def_RawBlending_UB_Policy

open RawBlending.UB

private def Jquad (w : Vec) : ℝ := w.1 ^ 2 + w.2 ^ 2

private lemma isJClass_Jquad : IsJClass Jquad := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- ConvexOn ℝ orthant Jquad
    refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha hb _
      have hx1 : (0 : ℝ) ≤ x.1 := hx.1
      have hx2 : (0 : ℝ) ≤ x.2 := hx.2
      have hy1 : (0 : ℝ) ≤ y.1 := hy.1
      have hy2 : (0 : ℝ) ≤ y.2 := hy.2
      exact ⟨by change (0 : ℝ) ≤ a * x.1 + b * y.1; nlinarith,
             by change (0 : ℝ) ≤ a * x.2 + b * y.2; nlinarith⟩
    · intro x _ y _ a b ha hb hab
      change (a * x.1 + b * y.1) ^ 2 + (a * x.2 + b * y.2) ^ 2 ≤
        a * (x.1 ^ 2 + x.2 ^ 2) + b * (y.1 ^ 2 + y.2 ^ 2)
      have hb' : b = 1 - a := by linarith
      have h1 : a * x.1 ^ 2 + b * y.1 ^ 2 - (a * x.1 + b * y.1) ^ 2 =
          a * b * (x.1 - y.1) ^ 2 := by rw [hb']; ring
      have h2 : a * x.2 ^ 2 + b * y.2 ^ 2 - (a * x.2 + b * y.2) ^ 2 =
          a * b * (x.2 - y.2) ^ 2 := by rw [hb']; ring
      have h1_nn : 0 ≤ a * b * (x.1 - y.1) ^ 2 := by positivity
      have h2_nn : 0 ≤ a * b * (x.2 - y.2) ^ 2 := by positivity
      linarith
  · -- ContinuousOn Jquad orthant
    exact ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousOn
  · -- SupermodularOn Jquad orthant
    intro x _ y _
    change x.1 ^ 2 + x.2 ^ 2 + (y.1 ^ 2 + y.2 ^ 2) ≤
      (max x.1 y.1) ^ 2 + (max x.2 y.2) ^ 2 + ((min x.1 y.1) ^ 2 + (min x.2 y.2) ^ 2)
    rcases le_total x.1 y.1 with h1 | h1 <;> rcases le_total x.2 y.2 with h2 | h2 <;>
      simp [h1, h2] <;> linarith
  · -- Tendsto in first coordinate
    intro v _
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨max b 1, fun s hs => ?_⟩
    have hs1 : 1 ≤ s := le_trans (le_max_right b 1) hs
    have hsb : b ≤ s := le_trans (le_max_left b 1) hs
    change b ≤ s ^ 2 + v ^ 2
    nlinarith [sq_nonneg v]
  · -- Tendsto in second coordinate
    intro v _
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨max b 1, fun s hs => ?_⟩
    have hs1 : 1 ≤ s := le_trans (le_max_right b 1) hs
    have hsb : b ≤ s := le_trans (le_max_left b 1) hs
    change b ≤ v ^ 2 + s ^ 2
    nlinarith [sq_nonneg v]

theorem solution :
    ¬ (∀ (Jobj : Vec → ℝ) (_hJ : IsJClass Jobj)
        (a1 a2 : ℝ) (_ha1 : 0 < a1) (_ha2 : a1 < a2),
        ∃ C : Curves, IsUBCurves Jobj a1 a2 C ∧
          ∀ D R : ℝ, 0 ≤ D → 0 ≤ R →
            RegionsCover C a1 a2 D R ∧
            (a1 * R < D → RegionsDisjoint C a1 a2 D R) ∧
            ∀ y : Vec, y ∈ orthant →
              Minimizes Jobj (E2 a1 a2 y D R) (ubAction C a1 a2 D R y)) := by
  intro h
  obtain ⟨C, hUB, hDR⟩ := h Jquad isJClass_Jquad 1 2 (by norm_num) (by norm_num)
  have hmin_wbar : Minimizes Jquad orthant C.wbar := hUB.2.2.2.2.2.2.2.1
  have hmin_alpha : ∀ x : ℝ, 0 ≤ x →
      Minimizes Jquad {w : Vec | w ∈ orthant ∧ (1 : ℝ) * w.1 + 2 * w.2 = x} (C.α x) :=
    hUB.2.2.2.2.2.2.2.2.2.2.1
  have hmin_beta : ∀ x : ℝ, 0 ≤ x →
      Minimizes Jquad {w : Vec | w ∈ orthant ∧ w.1 + w.2 = x} (C.β x) :=
    hUB.2.2.2.2.2.2.2.2.2.2.2
  -- Determine C.wbar = (0, 0)
  have hwbar0 : C.wbar.1 = 0 ∧ C.wbar.2 = 0 := by
    have h0 : (0, 0) ∈ orthant := ⟨le_refl 0, le_refl 0⟩
    have hle : C.wbar.1 ^ 2 + C.wbar.2 ^ 2 ≤ (0 : ℝ) ^ 2 + 0 ^ 2 := hmin_wbar.2 (0, 0) h0
    exact ⟨by nlinarith [sq_nonneg C.wbar.1, sq_nonneg C.wbar.2],
           by nlinarith [sq_nonneg C.wbar.1, sq_nonneg C.wbar.2]⟩
  -- Determine (C.α 5).1 = 1
  have halpha5 : (C.α 5).1 = 1 := by
    have hm := hmin_alpha 5 (by norm_num)
    have hfeas : ((1 : ℝ), (2 : ℝ)) ∈ {w : Vec | w ∈ orthant ∧ (1 : ℝ) * w.1 + 2 * w.2 = 5} := by
      refine ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    have hle : (C.α 5).1 ^ 2 + (C.α 5).2 ^ 2 ≤ (1 : ℝ) ^ 2 + 2 ^ 2 := hm.2 (1, 2) hfeas
    have heq : (1 : ℝ) * (C.α 5).1 + 2 * (C.α 5).2 = 5 := hm.1.2
    have hsq : ((C.α 5).1 - 1) ^ 2 + ((C.α 5).2 - 2) ^ 2 ≤ 0 := by nlinarith
    nlinarith [sq_nonneg ((C.α 5).1 - 1), sq_nonneg ((C.α 5).2 - 2)]
  -- Determine (C.β 7).1 = 7 / 2
  have hbeta7 : (C.β 7).1 = 7 / 2 := by
    have hm := hmin_beta 7 (by norm_num)
    have hfeas : ((7 / 2 : ℝ), (7 / 2 : ℝ)) ∈ {w : Vec | w ∈ orthant ∧ w.1 + w.2 = 7} := by
      refine ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    have hle : (C.β 7).1 ^ 2 + (C.β 7).2 ^ 2 ≤ (7 / 2 : ℝ) ^ 2 + (7 / 2 : ℝ) ^ 2 :=
      hm.2 (7 / 2, 7 / 2) hfeas
    have heq : (C.β 7).1 + (C.β 7).2 = 7 := hm.1.2
    have hsq : ((C.β 7).1 - 7 / 2) ^ 2 + ((C.β 7).2 - 7 / 2) ^ 2 ≤ 0 := by nlinarith
    nlinarith [sq_nonneg ((C.β 7).1 - 7 / 2), sq_nonneg ((C.β 7).2 - 7 / 2)]
  -- Specialize to D = 10, R = 1, where a1 * R = 1 < 10 = D and a2 * R = 2 ≤ 10 = D
  have hdisj : RegionsDisjoint C 1 2 10 1 :=
    (hDR 10 1 (by norm_num) (by norm_num)).2.1 (by norm_num)
  have hL1 : L1 1 2 10 1 = 0 := by
    simp [L1]
    norm_num
  have hL2 : L2 1 2 10 1 = 1 := by
    simp [L2, K2]
    norm_num
  -- Consider the strictly interior inventory point y = (1, 7)
  let y : Vec := (1, 7)
  have hy_orth : y ∈ orthant := ⟨by norm_num, by norm_num⟩
  have hy_not_R0 : y ∉ R0 C 1 2 10 1 := by
    intro hR0
    rcases hR0.2.1 with h1 | h2
    · rw [hwbar0.1, hL1] at h1; norm_num [y] at h1
    · rw [hwbar0.2, hL2] at h2; norm_num [y] at h2
  have hy_dem : exceedsDemand C 1 2 10 y := by
    simp only [exceedsDemand, hwbar0.1, hwbar0.2, y]
    norm_num
  have hy_cap : exceedsCapacity C 1 y := by
    simp only [exceedsCapacity, hwbar0.1, hwbar0.2, y]
    norm_num
  have hy_R1 : y ∈ region C 1 2 10 1 ⟨1, by omega⟩ := by
    apply Or.inl
    refine ⟨hy_orth, hy_not_R0, ?_, hy_dem⟩
    have h5 : (1 : ℝ) * y.1 + 2 * y.2 - 10 = 5 := by norm_num [y]
    rw [h5, halpha5]
  have hy_R3 : y ∈ region C 1 2 10 1 ⟨3, by omega⟩ := by
    apply Or.inr
    refine ⟨hy_orth, hy_not_R0, hy_dem, hy_cap, ?_, ?_⟩
    · have h5 : (1 : ℝ) * y.1 + 2 * y.2 - 10 = 5 := by norm_num [y]
      rw [h5, halpha5, hL1]
      norm_num [y]
    · have h7 : y.1 + y.2 - 1 = 7 := by norm_num [y]
      rw [h7, hbeta7, hL1]
      norm_num [y]
  have h13 : (⟨1, by omega⟩ : Fin 6) ≠ ⟨3, by omega⟩ := by decide
  exact Set.disjoint_left.mp (hdisj ⟨1, by omega⟩ ⟨3, by omega⟩ h13) hy_R1 hy_R3
