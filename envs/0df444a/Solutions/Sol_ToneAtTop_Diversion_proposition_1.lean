-- Prove2me | solution 1 for ToneAtTop.Diversion.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:28:27.340373+00:00
-- url     : https://prove2.me/submissions/480fb153-b480-4f5d-b085-eb1dca3f7c96

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

set_option autoImplicit false

namespace ToneAtTopDiv1Aux
open ToneAtTop.Diversion

lemma noncomp_iff (P : Params) (hγ : 0 < P.γ) (c x η : ℝ) :
    Noncompliant P c x η ↔ (1 - P.β) * η / P.γ < (1 - c) * x := by
  unfold Noncompliant utilCompliant utilNoncompliant
  rw [div_lt_iff₀ hγ]
  constructor <;> intro h <;> linarith

lemma diverted_eq (P : Params) (hγ : 0 < P.γ) (c x η : ℝ) :
    diverted P c x η = if (1 - P.β) * η / P.γ < (1 - c) * x then (1 - c) * x else 0 := by
  unfold diverted
  by_cases h : (1 - P.β) * η / P.γ < (1 - c) * x
  · rw [if_pos ((noncomp_iff P hγ c x η).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((noncomp_iff P hγ c x η).1 h')), if_neg h]

lemma mono_step (u t : ℝ) (hu : 0 ≤ u) (ht : 0 ≤ t) :
    Monotone (fun x : ℝ => if t < u * x then u * x else 0) := by
  intro x y hxy
  dsimp only
  have hm : u * x ≤ u * y := mul_le_mul_of_nonneg_left hxy hu
  split_ifs with h1 h2 h2
  · exact hm
  · exact absurd (lt_of_lt_of_le h1 hm) h2
  · linarith
  · exact le_refl _

lemma int_zero (u t b : ℝ) (hu : 0 < u) (hb0 : 0 ≤ b) (hb : u * b ≤ t) :
    ∫ x in (0:ℝ)..b, (if t < u * x then u * x else 0) = 0 := by
  have h : ∫ x in (0:ℝ)..b, (if t < u * x then u * x else 0) = ∫ x in (0:ℝ)..b, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hb0] at hx
    have hle : u * x ≤ t := le_trans (mul_le_mul_of_nonneg_left hx.2 hu.le) hb
    dsimp only
    rw [if_neg (not_lt.2 hle)]
  rw [h, intervalIntegral.integral_zero]

lemma int_pos (u t b : ℝ) (hu : 0 < u) (ht : 0 ≤ t) (hb : t < u * b) :
    ∫ x in (0:ℝ)..b, (if t < u * x then u * x else 0) = u * b ^ 2 / 2 - t ^ 2 / (2 * u) := by
  have hmono := mono_step u t hu.le ht
  have hT0 : 0 ≤ t / u := div_nonneg ht hu.le
  have huT : u * (t / u) = t := by field_simp
  have hTb : t / u < b := by
    rw [div_lt_iff₀ hu]; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := t / u)
    (hmono.intervalIntegrable) (hmono.intervalIntegrable)]
  have h1 : ∫ x in (0:ℝ)..(t / u), (if t < u * x then u * x else 0) = 0 :=
    int_zero u t (t / u) hu hT0 (le_of_eq huT)
  have h2 : ∫ x in (t / u)..b, (if t < u * x then u * x else 0) = ∫ x in (t / u)..b, u * x := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hTb.le] at hx
    have hlt : t < u * x := by
      have := mul_lt_mul_of_pos_left hx.1 hu
      rwa [huT] at this
    rw [if_pos hlt]
  rw [h1, h2, intervalIntegral.integral_const_mul, integral_id]
  field_simp
  ring

lemma int_ge (u t b : ℝ) (hu : 0 < u) (ht : 0 ≤ t) (hb0 : 0 ≤ b) (hb : t ≤ u * b) :
    ∫ x in (0:ℝ)..b, (if t < u * x then u * x else 0) = u * b ^ 2 / 2 - t ^ 2 / (2 * u) := by
  rcases lt_or_eq_of_le hb with h | h
  · exact int_pos u t b hu ht h
  · rw [int_zero u t b hu hb0 (le_of_eq h.symm), h]
    field_simp
    ring

lemma tau_pos (P : Params) (hS : P.Standing) : 0 < P.tau := by
  have h' := hS
  unfold Params.Standing at h'
  obtain ⟨_, _, _, _, hβ, hγ0, _, hη, _⟩ := h'
  unfold Params.tau
  exact div_pos (mul_pos (by linarith) hη) hγ0

lemma EL_eq (P : Params) (hS : P.Standing) (c : ℝ) (hc : c < 1) :
    expectedLoss P c =
      (P.p * (∫ x in (0:ℝ)..P.xbar, (if P.tau < (1 - c) * x then (1 - c) * x else 0))
        + (1 - P.p) * ((1 - c) * P.xbar ^ 2 / 2)) / P.xbar + P.lam / (1 - c) := by
  have h' := hS
  unfold Params.Standing at h'
  obtain ⟨hx, _, _, _, _, hγ0, _, _, _⟩ := h'
  have hu : 0 < 1 - c := by linarith
  have hτ : 0 < P.tau := tau_pos P hS
  have eH : ∀ x, diverted P c x P.ηH = if P.tau < (1 - c) * x then (1 - c) * x else 0 :=
    fun x => diverted_eq P hγ0 c x P.ηH
  have e0 : ∀ x, diverted P c x 0 = if (0:ℝ) < (1 - c) * x then (1 - c) * x else 0 := by
    intro x
    rw [diverted_eq P hγ0 c x 0, mul_zero, zero_div]
  have I0 := int_ge (1 - c) 0 P.xbar hu le_rfl hx.le (mul_pos hu hx).le
  have mH := mono_step (1 - c) P.tau hu.le hτ.le
  have m0 := mono_step (1 - c) 0 hu.le le_rfl
  unfold expectedLoss costK
  simp_rw [eH, e0]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      ((mH.intervalIntegrable).const_mul _) ((m0.intervalIntegrable).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, I0]
  ring

lemma EL_hi (P : Params) (hS : P.Standing) (c : ℝ) (hc : c < 1)
    (h : P.tau ≤ (1 - c) * P.xbar) :
    expectedLoss P c = (1 - c) * P.xbar / 2 +
      (2 * P.lam * P.xbar - P.p * P.tau ^ 2) / (2 * ((1 - c) * P.xbar)) := by
  have h' := hS
  unfold Params.Standing at h'
  obtain ⟨hx, _, _, _, _, _, _, _, _⟩ := h'
  have hu : 0 < 1 - c := by linarith
  have hτ : 0 < P.tau := tau_pos P hS
  rw [EL_eq P hS c hc, int_ge (1 - c) P.tau P.xbar hu hτ.le hx.le h]
  have : (1 - c) ≠ 0 := hu.ne'
  have : P.xbar ≠ 0 := hx.ne'
  field_simp
  ring

lemma EL_lo (P : Params) (hS : P.Standing) (c : ℝ) (hc : c < 1)
    (h : (1 - c) * P.xbar ≤ P.tau) :
    expectedLoss P c = (1 - P.p) * ((1 - c) * P.xbar) / 2 +
      P.lam * P.xbar / ((1 - c) * P.xbar) := by
  have h' := hS
  unfold Params.Standing at h'
  obtain ⟨hx, _, _, _, _, _, _, _, _⟩ := h'
  have hu : 0 < 1 - c := by linarith
  rw [EL_eq P hS c hc, int_zero (1 - c) P.tau P.xbar hu hx.le h]
  have : (1 - c) ≠ 0 := hu.ne'
  have : P.xbar ≠ 0 := hx.ne'
  field_simp
  ring

end ToneAtTopDiv1Aux

open ToneAtTopDiv1Aux

open ToneAtTop.Diversion in
theorem solution (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p))
    (hL1b : 1 - 2 * P.lam * P.xbar / P.tau ^ 2 < P.p)
    (hc0 : 2 * P.lam * P.xbar - P.p * P.tau ^ 2 ≤ P.xbar ^ 2) :
    (P.tau ≤ Real.sqrt (2 * P.lam * P.xbar / (1 + P.p)) →
      let c₁ := 1 - Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) / P.xbar
      c₁ ∈ Set.Ico (0 : ℝ) 1 ∧
      (∀ c ∈ Set.Ico (0 : ℝ) 1, c ≠ c₁ → expectedLoss P c₁ < expectedLoss P c) ∧
      tippingPoint P c₁ =
        P.tau * P.xbar / Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2)) ∧
    (Real.sqrt (2 * P.lam * P.xbar / (1 + P.p)) ≤ P.tau →
      let c₂ := 1 - P.tau / P.xbar
      c₂ ∈ Set.Ico (0 : ℝ) 1 ∧
      (∀ c ∈ Set.Ico (0 : ℝ) 1, c ≠ c₂ → expectedLoss P c₂ < expectedLoss P c) ∧
      tippingPoint P c₂ = P.xbar) := by
  have h' := hS
  unfold Params.Standing at h'
  obtain ⟨hx, hl, hp0, hp1, _, _, _, _, hτx⟩ := h'
  have hτ : 0 < P.tau := tau_pos P hS
  have hK0 : 0 < 2 * P.lam * P.xbar - P.p * P.tau ^ 2 := by
    have h1 : P.tau ^ 2 < 2 * P.lam * P.xbar / P.p := by
      have := pow_lt_pow_left₀ hL1a hτ.le two_ne_zero
      rwa [Real.sq_sqrt (by positivity)] at this
    rw [lt_div_iff₀ hp0] at h1
    linarith
  have hL1b' : (1 - P.p) * P.tau ^ 2 < 2 * P.lam * P.xbar := by
    have h2 : 1 - P.p < 2 * P.lam * P.xbar / P.tau ^ 2 := by linarith
    rwa [lt_div_iff₀ (by positivity)] at h2
  set K := 2 * P.lam * P.xbar - P.p * P.tau ^ 2 with hK
  constructor
  · intro hq
    have hτK : P.tau ^ 2 ≤ K := by
      have := pow_le_pow_left₀ hτ.le hq 2
      rw [Real.sq_sqrt (by positivity), le_div_iff₀ (by linarith)] at this
      rw [hK]; nlinarith
    set s := Real.sqrt K with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hK0
    have hss : s ^ 2 = K := Real.sq_sqrt hK0.le
    have hτs : P.tau ≤ s := by
      rw [hs]
      calc P.tau = Real.sqrt (P.tau ^ 2) := (Real.sqrt_sq hτ.le).symm
        _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hτK
    have hsx : s ≤ P.xbar := by
      rw [hs]
      calc Real.sqrt K ≤ Real.sqrt (P.xbar ^ 2) := Real.sqrt_le_sqrt hc0
        _ = P.xbar := Real.sqrt_sq hx.le
    dsimp only
    have hu1 : 1 - (1 - s / P.xbar) = s / P.xbar := by ring
    have hy1 : (1 - (1 - s / P.xbar)) * P.xbar = s := by rw [hu1]; field_simp
    have hlt1 : (1 - s / P.xbar) < 1 := by have : 0 < s / P.xbar := div_pos hs0 hx; linarith
    have hL1 : expectedLoss P (1 - s / P.xbar) = s := by
      rw [EL_hi P hS _ hlt1 (by rw [hy1]; exact hτs), hy1, ← hK, ← hss]
      field_simp
      ring
    refine ⟨⟨?_, hlt1⟩, ?_, ?_⟩
    · have : s / P.xbar ≤ 1 := (div_le_one hx).2 hsx
      linarith
    · rintro c ⟨_, hc1'⟩ hne
      rw [hL1]
      have hu : 0 < 1 - c := by linarith
      have hy0 : 0 < (1 - c) * P.xbar := mul_pos hu hx
      have hys : (1 - c) * P.xbar ≠ s := by
        intro h; apply hne
        rw [← h, mul_div_assoc, div_self hx.ne', mul_one]; ring
      have hLA : (1 - c) * P.xbar / 2 + K / (2 * ((1 - c) * P.xbar)) ≤ expectedLoss P c := by
        rcases le_or_gt P.tau ((1 - c) * P.xbar) with h | h
        · rw [EL_hi P hS c hc1' h, ← hK]
        · rw [EL_lo P hS c hc1' h.le, hK]
          have e : (1 - P.p) * ((1 - c) * P.xbar) / 2 + P.lam * P.xbar / ((1 - c) * P.xbar) -
              ((1 - c) * P.xbar / 2 + (2 * P.lam * P.xbar - P.p * P.tau ^ 2) /
                (2 * ((1 - c) * P.xbar))) =
              P.p * (P.tau ^ 2 - ((1 - c) * P.xbar) ^ 2) / (2 * ((1 - c) * P.xbar)) := by
            have : (1 - c) ≠ 0 := hu.ne'
            have : P.xbar ≠ 0 := hx.ne'
            field_simp
            ring
          have hnn : 0 ≤ P.p * (P.tau ^ 2 - ((1 - c) * P.xbar) ^ 2) / (2 * ((1 - c) * P.xbar)) := by
            apply div_nonneg _ (mul_pos two_pos hy0).le
            apply mul_nonneg hp0.le
            nlinarith [mul_pos (sub_pos.2 h) (add_pos hτ hy0)]
          linarith
      have hgt : s < (1 - c) * P.xbar / 2 + K / (2 * ((1 - c) * P.xbar)) := by
        have e : (1 - c) * P.xbar / 2 + K / (2 * ((1 - c) * P.xbar)) - s =
            ((1 - c) * P.xbar - s) ^ 2 / (2 * ((1 - c) * P.xbar)) := by
          rw [← hss]
          have : (1 - c) ≠ 0 := hu.ne'
          have : P.xbar ≠ 0 := hx.ne'
          field_simp
          ring
        have hp : 0 < ((1 - c) * P.xbar - s) ^ 2 / (2 * ((1 - c) * P.xbar)) := by
          apply div_pos _ (mul_pos two_pos hy0)
          exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hys)))
        linarith
      linarith
    · unfold tippingPoint
      rw [hu1, div_div_eq_mul_div]
  · intro hq
    have hKτ : K ≤ P.tau ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hq 2
      rw [Real.sq_sqrt (by positivity), div_le_iff₀ (by linarith)] at this
      rw [hK]; nlinarith
    dsimp only
    have hu2 : 1 - (1 - P.tau / P.xbar) = P.tau / P.xbar := by ring
    have hy2 : (1 - (1 - P.tau / P.xbar)) * P.xbar = P.tau := by rw [hu2]; field_simp
    have hlt2 : 1 - P.tau / P.xbar < 1 := by have := div_pos hτ hx; linarith
    refine ⟨⟨?_, hlt2⟩, ?_, ?_⟩
    · have : P.tau / P.xbar ≤ 1 := (div_le_one hx).2 hτx.le
      linarith
    · rintro c ⟨_, hc1'⟩ hne
      have hu : 0 < 1 - c := by linarith
      have hy0 : 0 < (1 - c) * P.xbar := mul_pos hu hx
      have hyτ : (1 - c) * P.xbar ≠ P.tau := by
        intro h; apply hne
        rw [← h, mul_div_assoc, div_self hx.ne', mul_one]; ring
      have hden : 0 < 2 * ((1 - c) * P.xbar) * P.tau := mul_pos (mul_pos two_pos hy0) hτ
      rcases lt_or_gt_of_ne hyτ with h | h
      · rw [EL_lo P hS c hc1' h.le, EL_lo P hS _ hlt2 (le_of_eq hy2), hy2]
        have e : (1 - P.p) * ((1 - c) * P.xbar) / 2 + P.lam * P.xbar / ((1 - c) * P.xbar) -
            ((1 - P.p) * P.tau / 2 + P.lam * P.xbar / P.tau) =
            (P.tau - (1 - c) * P.xbar) *
              (2 * P.lam * P.xbar - (1 - P.p) * ((1 - c) * P.xbar) * P.tau) /
              (2 * ((1 - c) * P.xbar) * P.tau) := by
          have : (1 - c) ≠ 0 := hu.ne'
          have : P.xbar ≠ 0 := hx.ne'
          have : P.tau ≠ 0 := hτ.ne'
          field_simp
          ring
        have hp : 0 < (P.tau - (1 - c) * P.xbar) *
              (2 * P.lam * P.xbar - (1 - P.p) * ((1 - c) * P.xbar) * P.tau) /
              (2 * ((1 - c) * P.xbar) * P.tau) := by
          apply div_pos _ hden
          apply mul_pos (by linarith)
          nlinarith [mul_lt_mul_of_pos_left h (mul_pos (sub_pos.2 hp1) hτ)]
        linarith
      · rw [EL_hi P hS c hc1' h.le, EL_hi P hS _ hlt2 (le_of_eq hy2.symm), hy2, ← hK]
        have e : (1 - c) * P.xbar / 2 + K / (2 * ((1 - c) * P.xbar)) -
            (P.tau / 2 + K / (2 * P.tau)) =
            ((1 - c) * P.xbar - P.tau) * ((1 - c) * P.xbar * P.tau - K) /
              (2 * ((1 - c) * P.xbar) * P.tau) := by
          have : (1 - c) ≠ 0 := hu.ne'
          have : P.xbar ≠ 0 := hx.ne'
          have : P.tau ≠ 0 := hτ.ne'
          field_simp
          ring
        have hp : 0 < ((1 - c) * P.xbar - P.tau) * ((1 - c) * P.xbar * P.tau - K) /
              (2 * ((1 - c) * P.xbar) * P.tau) := by
          apply div_pos _ hden
          apply mul_pos (by linarith)
          nlinarith [mul_lt_mul_of_pos_right h hτ]
        linarith
    · unfold tippingPoint
      rw [hu2, div_div_eq_mul_div]
      field_simp
