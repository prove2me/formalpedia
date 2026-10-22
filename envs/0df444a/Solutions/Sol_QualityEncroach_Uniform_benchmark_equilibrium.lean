-- Prove2me | solution 1 for QualityEncroach.Uniform.benchmark_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:23.073735+00:00
-- url     : https://prove2.me/submissions/a578fbd8-343e-4378-8f36-39d607ea4f16

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

set_option autoImplicit false
open QualityEncroach.Uniform

lemma qq_pay (w u q : ℝ) (hu : 0 < u) :
    benchRetailerPayoff ⟨w, u, q⟩ = u * (qRN w u) ^ 2 - u * (q - qRN w u) ^ 2 := by
  unfold benchRetailerPayoff qRN
  field_simp
  ring

lemma qq_ret_best (w u : ℝ) (hu : 0 < u) (q : ℝ) (hq : 0 ≤ q) :
    benchRetailerPayoff ⟨w, u, q⟩ ≤ benchRetailerPayoff ⟨w, u, max 0 (qRN w u)⟩ := by
  rw [qq_pay w u q hu, qq_pay w u _ hu]
  rcases le_total 0 (qRN w u) with h | h
  · rw [max_eq_right h]
    have : 0 ≤ u * (q - qRN w u) ^ 2 := by positivity
    nlinarith
  · rw [max_eq_left h]
    have h3 : 0 ≤ u * (q * (q - 2 * qRN w u)) :=
      mul_nonneg hu.le (mul_nonneg hq (by linarith))
    nlinarith

lemma qq_ret_unique (w u o : ℝ) (hu : 0 < u) (ho : 0 ≤ o)
    (h : ∀ q : ℝ, 0 ≤ q → benchRetailerPayoff ⟨w, u, q⟩ ≤ benchRetailerPayoff ⟨w, u, o⟩) :
    o = max 0 (qRN w u) := by
  have h1 := h _ (le_max_left 0 (qRN w u))
  rw [qq_pay w u _ hu, qq_pay w u o hu] at h1
  rcases le_total 0 (qRN w u) with hb | hb
  · rw [max_eq_right hb] at h1 ⊢
    have h2 : (o - qRN w u) ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos hu hc]
    have : o - qRN w u = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
    linarith
  · rw [max_eq_left hb] at h1 ⊢
    have h2 : o * (o - 2 * qRN w u) ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos hu hc]
    have h3 : 0 ≤ o * (-(2 * qRN w u)) := mul_nonneg ho (by linarith)
    have h4 : o * o ≤ 0 := by nlinarith
    nlinarith

lemma qq_mfr (k : ℝ) (hk : 0 < k) (w u : ℝ) (hu : 0 < u) :
    (w - k * u ^ 2) * max 0 (qRN w u) ≤ 1 / (54 * k) ∧
    (1 / (54 * k) ≤ (w - k * u ^ 2) * max 0 (qRN w u) →
      u = 1 / (3 * k) ∧ w = 2 / (9 * k)) := by
  have hpos : 0 < 1 / (54 * k) := by positivity
  rcases le_total (qRN w u) 0 with hb | hb
  · rw [max_eq_left hb]
    simp only [mul_zero]
    exact ⟨hpos.le, fun h => absurd h (not_le.2 hpos)⟩
  · rw [max_eq_right hb]
    have hid : (w - k * u ^ 2) * qRN w u = 1 / (54 * k) - (w - wN k u) ^ 2 / (2 * u)
        - (k * u - 1 / 3) ^ 2 * (4 / 3 - k * u) / (8 * k) := by
      unfold qRN wN
      field_simp
      ring
    by_cases hku : k * u < 1
    · have E2 : 0 ≤ (k * u - 1 / 3) ^ 2 * (4 / 3 - k * u) / (8 * k) :=
        div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity)
      have E1 : 0 ≤ (w - wN k u) ^ 2 / (2 * u) := by positivity
      refine ⟨by linarith, fun h => ?_⟩
      have hE1 : (w - wN k u) ^ 2 / (2 * u) = 0 := by linarith
      have hE2 : (k * u - 1 / 3) ^ 2 * (4 / 3 - k * u) / (8 * k) = 0 := by linarith
      have hE1' : (w - wN k u) ^ 2 = 0 := by
        rcases div_eq_zero_iff.1 hE1 with h' | h'
        · exact h'
        · exact absurd h' (by positivity)
      have hE2' : (k * u - 1 / 3) ^ 2 * (4 / 3 - k * u) = 0 := by
        rcases div_eq_zero_iff.1 hE2 with h' | h'
        · exact h'
        · exact absurd h' (by positivity)
      have hu1 : k * u - 1 / 3 = 0 := by
        rcases mul_eq_zero.1 hE2' with h' | h'
        · exact pow_eq_zero_iff two_ne_zero |>.1 h'
        · exact absurd h' (by linarith)
      have hw1 : w - wN k u = 0 := pow_eq_zero_iff two_ne_zero |>.1 hE1'
      have hu2 : u = 1 / (3 * k) := by
        field_simp
        linarith
      refine ⟨hu2, ?_⟩
      have : w = wN k u := by linarith
      rw [this, hu2]
      unfold wN
      field_simp
      ring
    · push_neg at hku
      have hw : w ≤ u := by
        have := hb
        unfold qRN at this
        rw [sub_nonneg, div_le_iff₀ (by positivity)] at this
        linarith
      have h1 : w - k * u ^ 2 ≤ 0 := by nlinarith [mul_nonneg hu.le (sub_nonneg.2 hku)]
      have h2 : (w - k * u ^ 2) * qRN w u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 hb
      exact ⟨by linarith, fun h => absurd (le_trans h h2) (not_le.2 hpos)⟩

theorem solution (k : ℝ) (hk : 0 < k) :
    (∃ τ : BenchProfile, IsBenchSPE k τ) ∧
    ∀ τ : BenchProfile, IsBenchSPE k τ →
      τ.u = 1 / (3 * k) ∧ τ.w = 2 / (9 * k) ∧ τ.path.qR = 1 / 6 ∧
      benchMfrPayoff k τ.path = 1 / (54 * k) ∧
      benchRetailerPayoff τ.path = 1 / (108 * k) := by
  have hq6 : qRN (2 / (9 * k)) (1 / (3 * k)) = 1 / 6 := by
    unfold qRN; field_simp; ring
  have hm6 : (2 / (9 * k) - k * (1 / (3 * k)) ^ 2) * (1 / 6) = 1 / (54 * k) := by
    field_simp; ring
  have hr6 : (1 / (3 * k) * (1 - 1 / 6) - 2 / (9 * k)) * (1 / 6) = 1 / (108 * k) := by
    field_simp; ring
  have hu0 : 0 < 1 / (3 * k) := by positivity
  refine ⟨⟨⟨2 / (9 * k), 1 / (3 * k), fun w u => max 0 (qRN w u)⟩, ?_⟩, ?_⟩
  · refine ⟨fun w u hu => ⟨le_max_left _ _, fun q hq => qq_ret_best w u hu q hq⟩, hu0, ?_⟩
    intro w u hu
    have := (qq_mfr k hk w u hu).1
    have e : benchMfrPayoff k (BenchProfile.path ⟨2 / (9 * k), 1 / (3 * k), fun w u => max 0 (qRN w u)⟩)
        = 1 / (54 * k) := by
      show (2 / (9 * k) - k * (1 / (3 * k)) ^ 2) * max 0 (qRN (2 / (9 * k)) (1 / (3 * k))) = _
      rw [hq6, max_eq_right (by norm_num), hm6]
    rw [e]
    exact this
  · intro τ ⟨hret, hτu, hM⟩
    have hord : ∀ w u : ℝ, 0 < u → τ.order w u = max 0 (qRN w u) := fun w u hu =>
      qq_ret_unique w u _ hu (hret w u hu).1 (hret w u hu).2
    have h1 := hM (2 / (9 * k)) (1 / (3 * k)) hu0
    have e1 : benchMfrPayoff k (τ.outcomeAt (2 / (9 * k)) (1 / (3 * k))) = 1 / (54 * k) := by
      show (2 / (9 * k) - k * (1 / (3 * k)) ^ 2) * τ.order (2 / (9 * k)) (1 / (3 * k)) = _
      rw [hord _ _ hu0, hq6, max_eq_right (by norm_num), hm6]
    have e2 : benchMfrPayoff k τ.path = (τ.w - k * τ.u ^ 2) * max 0 (qRN τ.w τ.u) := by
      show (τ.w - k * τ.u ^ 2) * τ.order τ.w τ.u = _
      rw [hord _ _ hτu]
    rw [e1, e2] at h1
    obtain ⟨hu', hw'⟩ := (qq_mfr k hk τ.w τ.u hτu).2 h1
    have hq : τ.path.qR = 1 / 6 := by
      show τ.order τ.w τ.u = 1 / 6
      rw [hord _ _ hτu, hw', hu', hq6]
      norm_num
    refine ⟨hu', hw', hq, ?_, ?_⟩
    · show (τ.w - k * τ.u ^ 2) * τ.order τ.w τ.u = _
      change (τ.w - k * τ.u ^ 2) * τ.path.qR = _
      rw [hq, hw', hu']
      field_simp; ring
    · show (τ.u * (1 - τ.path.qR) - τ.w) * τ.path.qR = _
      rw [hq, hw', hu']
      exact hr6
