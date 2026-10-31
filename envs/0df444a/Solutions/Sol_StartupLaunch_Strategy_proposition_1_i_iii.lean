-- Prove2me | solution 1 for StartupLaunch.Strategy.proposition_1_i_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:12:36.087+00:00
-- url     : https://prove2.me/submissions/5b314d6f-8c7f-489f-92b4-caadc064090e

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

open StartupLaunch.Strategy

namespace StartupP1Aux

theorem slope (P : Params) (q x y : ℝ) : piLC P q x - piLC P q y = (1 - q) * P.δ * (x - y) := by
  unfold piLC; ring

theorem slopeD (P : Params) (q x y : ℝ) : piDC P q x - piDC P q y = (1 - q) * P.δ * (x - y) := by
  unfold piDC; ring

theorem ls_suff (P : Params) (hP : P.Standing) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h1 : piLC P q (piLS P) ≤ piLS P) (h2 : piDC P q (piLS P) ≤ piLS P) : EstLaunchStop P q := by
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP
  have hB1 : (1 - q) * P.δ < 1 := by nlinarith
  have hB0 : 0 ≤ (1 - q) * P.δ := mul_nonneg (by linarith) hδ0.le
  intro Pi0 Pi1 hB
  obtain ⟨e0, e1⟩ := hB
  have hge1 : piLS P ≤ Pi1 := (le_max_left (piLS P) (piLC P q Pi1)).trans (le_of_eq e1.symm)
  have hPi1 : Pi1 = piLS P := by
    by_contra hne
    have hgt : piLS P < Pi1 := lt_of_le_of_ne hge1 (Ne.symm hne)
    have hfix : Pi1 = piLC P q Pi1 := by
      rcases max_choice (piLS P) (piLC P q Pi1) with h | h
      · exact absurd (e1.trans h) hne
      · exact e1.trans h
    have := slope P q Pi1 (piLS P)
    nlinarith [mul_lt_mul_of_pos_right hB1 (sub_pos.2 hgt)]
  rw [← e1] at e0
  have hge0 : Pi1 ≤ Pi0 := (le_max_left Pi1 (piDC P q Pi0)).trans (le_of_eq e0.symm)
  refine ⟨?_, hPi1⟩
  by_contra hne
  rw [hPi1] at hge0 e0
  have hgt : piLS P < Pi0 := lt_of_le_of_ne hge0 (Ne.symm hne)
  have hfix : Pi0 = piDC P q Pi0 := by
    rcases max_choice (piLS P) (piDC P q Pi0) with h | h
    · exact absurd (e0.trans h) hne
    · exact e0.trans h
  have := slopeD P q Pi0 (piLS P)
  nlinarith [mul_lt_mul_of_pos_right hB1 (sub_pos.2 hgt)]

theorem lc_suff (P : Params) (hP : P.Standing) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h1 : piLS P ≤ piLC P q (piLS P)) (h3 : ∀ x, piDC P q x ≤ piLC P q x) :
    EstLaunchContinue P q := by
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP
  have hB1 : (1 - q) * P.δ < 1 := by nlinarith
  have hB0 : 0 ≤ (1 - q) * P.δ := mul_nonneg (by linarith) hδ0.le
  intro Pi0 Pi1 hB
  obtain ⟨e0, e1⟩ := hB
  have hge1 : piLS P ≤ Pi1 := (le_max_left (piLS P) (piLC P q Pi1)).trans (le_of_eq e1.symm)
  have hfix : Pi1 = piLC P q Pi1 := by
    rcases max_choice (piLS P) (piLC P q Pi1) with h | h
    · have hv : Pi1 = piLS P := e1.trans h
      have := slope P q Pi1 (piLS P)
      rw [hv] at this ⊢
      apply le_antisymm h1
      rw [hv] at e1
      exact (le_max_right (piLS P) (piLC P q (piLS P))).trans (le_of_eq e1.symm)
    · exact e1.trans h
  rw [← e1] at e0
  have hge0 : Pi1 ≤ Pi0 := (le_max_left Pi1 (piDC P q Pi0)).trans (le_of_eq e0.symm)
  have hPi0 : Pi0 = Pi1 := by
    by_contra hne
    have hgt : Pi1 < Pi0 := lt_of_le_of_ne hge0 (Ne.symm hne)
    have hfix0 : Pi0 = piDC P q Pi0 := by
      rcases max_choice Pi1 (piDC P q Pi0) with h | h
      · exact absurd (e0.trans h) hne
      · exact e0.trans h
    have := slopeD P q Pi0 Pi1
    have := h3 Pi1
    nlinarith [mul_lt_mul_of_pos_right hB1 (sub_pos.2 hgt)]
  exact ⟨hPi0.trans hfix, hfix⟩

theorem dc_suff (P : Params) (hP : P.Standing) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h2 : piLS P ≤ piDC P q (piLS P)) (h3 : ∀ x, piLC P q x ≤ piDC P q x) :
    EstDeferContinue P q := by
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP
  have hB0 : 0 ≤ (1 - q) * P.δ := mul_nonneg (by linarith) hδ0.le
  intro Pi0 Pi1 hB
  obtain ⟨e0, e1⟩ := hB
  have hge1 : piLS P ≤ Pi1 := (le_max_left (piLS P) (piLC P q Pi1)).trans (le_of_eq e1.symm)
  rw [← e1] at e0
  have hge0 : Pi1 ≤ Pi0 := (le_max_left Pi1 (piDC P q Pi0)).trans (le_of_eq e0.symm)
  rcases max_choice Pi1 (piDC P q Pi0) with h | h
  · -- Pi0 = Pi1; show piDC Pi1 ≥ Pi1
    have hv : Pi0 = Pi1 := e0.trans h
    have hle : piDC P q Pi0 ≤ Pi0 :=
      (le_max_right Pi1 (piDC P q Pi0)).trans (le_of_eq e0.symm)
    apply le_antisymm _ hle
    rw [hv]
    rcases max_choice (piLS P) (piLC P q Pi1) with h' | h'
    · have hv1 : Pi1 = piLS P := e1.trans h'
      rw [hv1]; exact h2
    · have hv1 : Pi1 = piLC P q Pi1 := e1.trans h'
      calc Pi1 = piLC P q Pi1 := hv1
        _ ≤ piDC P q Pi1 := h3 Pi1
  · exact e0.trans h

end StartupP1Aux

open StartupP1Aux in
theorem solution (P : Params) (hP : P.Standing) :
    ∃ p1 p2 : ℝ, IsThresholds P p1 p2 := by
  have hP' := hP
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP'
  have hvoeq : P.vo - piLS P * (1 - P.δ) = 0 := by
    have h1d : (1 : ℝ) - P.δ ≠ 0 := by linarith
    unfold piLS Params.Vo; field_simp; ring
  have hVaVo : piLS P ≤ P.Va := by
    unfold piLS Params.Vo Params.Va; exact div_le_div_of_nonneg_right hvova (by linarith)
  have hVo : 0 < piLS P := by unfold piLS Params.Vo; exact div_pos hvo (by linarith)
  obtain ⟨s, hsd⟩ : ∃ s, s = (1 - P.α) * P.δ * P.Va - P.δ * piLS P := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t, t = P.δ * P.Va - P.δ * piLS P := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u, u = P.α * P.δ * P.Va := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [htd]; nlinarith
  have hu0 : 0 ≤ u := by rw [hud]; exact mul_nonneg (mul_nonneg hα0 hδ0.le) (by linarith)
  have e1 : ∀ q, piLC P q (piLS P) - piLS P = -P.c + q * s := by
    intro q; unfold piLC; rw [hsd]; linear_combination hvoeq
  have e2 : ∀ q, piDC P q (piLS P) - piLS P = -P.c - P.vo + q * t := by
    intro q; unfold piDC; rw [htd]; linear_combination hvoeq
  have e3 : ∀ q x, piLC P q x - piDC P q x = P.vo - q * u := by
    intro q x; unfold piLC piDC; rw [hud]; ring
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = if 0 < s then P.c / s else 1 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = if 0 < t then (P.c + P.vo) / t else 1 := ⟨_, rfl⟩
  obtain ⟨p1, hp1d⟩ : ∃ p1 : ℝ, p1 = min 1 (min r1 r2) := ⟨_, rfl⟩
  obtain ⟨p2, hp2d⟩ : ∃ p2 : ℝ, p2 = if u ≤ P.vo then 1 else max p1 (P.vo / u) := ⟨_, rfl⟩
  have hp1le : p1 ≤ 1 := by rw [hp1d]; exact min_le_left _ _
  -- below p1: both launch-continue and defer values are ≤ Vo
  have hbelow1 : ∀ q, 0 ≤ q → q ≤ p1 → -P.c + q * s ≤ 0 := by
    intro q hq0 hq
    have hqr : q ≤ r1 := hq.trans (by rw [hp1d]; exact (min_le_right _ _).trans (min_le_left _ _))
    by_cases hs : 0 < s
    · rw [hr1, if_pos hs, le_div_iff₀ hs] at hqr; linarith
    · push_neg at hs; nlinarith [mul_nonpos_of_nonneg_of_nonpos hq0 hs]
  have hbelow2 : ∀ q, 0 ≤ q → q ≤ p1 → -P.c - P.vo + q * t ≤ 0 := by
    intro q hq0 hq
    have hqr : q ≤ r2 := hq.trans (by rw [hp1d]; exact (min_le_right _ _).trans (min_le_right _ _))
    by_cases hs : 0 < t
    · rw [hr2, if_pos hs, le_div_iff₀ hs] at hqr; linarith
    · have : t = 0 := le_antisymm (not_lt.1 hs) ht0
      rw [this]; linarith
  have habove : ∀ q, q ≤ 1 → p1 < q → 0 < -P.c + q * s ∨ 0 < -P.c - P.vo + q * t := by
    intro q hq1 hq
    rw [hp1d] at hq
    rcases min_lt_iff.1 hq with h | h
    · linarith
    rcases min_lt_iff.1 h with h | h
    · left
      by_cases hs : 0 < s
      · rw [hr1, if_pos hs, div_lt_iff₀ hs] at h; linarith
      · rw [hr1, if_neg hs] at h; linarith
    · right
      by_cases hs : 0 < t
      · rw [hr2, if_pos hs, div_lt_iff₀ hs] at h; linarith
      · rw [hr2, if_neg hs] at h; linarith
  refine ⟨p1, p2, ?_, hp1le, ?_, ?_⟩
  · rw [hp2d]; split_ifs
    · exact hp1le
    · exact le_max_left _ _
  · intro h1
    rw [hp2d]; split_ifs with hu
    · rfl
    · push_neg at hu
      have : P.vo / u < 1 := (div_lt_one (by linarith)).2 hu
      rw [h1]; exact max_eq_left this.le
  · intro q hq0 hq1
    refine ⟨fun hq => ?_, fun hq hq2 => ?_, fun hq => ?_⟩
    · apply ls_suff P hP q hq0 hq1
      · linarith [e1 q, hbelow1 q hq0 hq]
      · linarith [e2 q, hbelow2 q hq0 hq]
    · have h3 : 0 ≤ P.vo - q * u := by
        rw [hp2d] at hq2
        split_ifs at hq2 with hu
        · nlinarith
        · push_neg at hu
          have hu0' : 0 < u := by linarith
          rcases le_total p1 (P.vo / u) with hm | hm
          · rw [max_eq_right hm, le_div_iff₀ hu0'] at hq2; linarith
          · rw [max_eq_left hm] at hq2; linarith
      apply lc_suff P hP q hq0 hq1
      · rcases habove q hq1 hq with h | h
        · linarith [e1 q]
        · have := e3 q (piLS P); linarith [e2 q]
      · intro x; have := e3 q x; linarith
    · have hp12 : p1 ≤ p2 := by
        rw [hp2d]; split_ifs
        · exact hp1le
        · exact le_max_left _ _
      have h3 : P.vo - q * u ≤ 0 := by
        rw [hp2d] at hq
        split_ifs at hq with hu
        · linarith
        · push_neg at hu
          have hu0' : 0 < u := by linarith
          have := (le_max_right p1 (P.vo / u)).trans_lt hq
          rw [div_lt_iff₀ hu0'] at this; linarith
      apply dc_suff P hP q hq0 hq1
      · rcases habove q hq1 (lt_of_le_of_lt hp12 hq) with h | h
        · have := e3 q (piLS P); linarith [e1 q]
        · linarith [e2 q]
      · intro x; have := e3 q x; linarith
