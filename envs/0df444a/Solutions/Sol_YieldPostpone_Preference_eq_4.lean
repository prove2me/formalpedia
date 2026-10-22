-- Prove2me | solution 1 for YieldPostpone.Preference.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:11:43.231899+00:00
-- url     : https://prove2.me/submissions/ee1c69ac-c769-49fe-b47c-f804966d8ef5

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting
set_option autoImplicit false
open YieldPostpone.Preference

noncomputable def llG (θ α w c q Q : ℝ) : ℝ :=
  θ * (w * min (1 * Q) q) + (1 - θ) * (w * min (α * Q) q) - c * Q

theorem llG_low {θ α w c q Q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hQ : 0 ≤ Q) (hq : Q ≤ q) :
    llG θ α w c q Q = (w * (α * (1 - θ) + θ) - c) * Q := by
  unfold llG
  have h1 : min (1 * Q) q = Q := by rw [one_mul]; exact min_eq_left hq
  have h2 : min (α * Q) q = α * Q := min_eq_left (by nlinarith)
  rw [h1, h2]; ring

theorem llG_mid {θ α w c q Q : ℝ} (hα : 0 < α) (hq : q ≤ Q) (hQ : α * Q ≤ q) :
    llG θ α w c q Q = θ * w * q + ((1 - θ) * w * α - c) * Q := by
  unfold llG
  have h1 : min (1 * Q) q = q := by rw [one_mul]; exact min_eq_right hq
  have h2 : min (α * Q) q = α * Q := min_eq_left hQ
  rw [h1, h2]; ring

theorem llG_high {θ α w c q Q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 ≤ q) (hQ : q ≤ α * Q) :
    llG θ α w c q Q = w * q - c * Q := by
  unfold llG
  have h1 : min (1 * Q) q = q := by rw [one_mul]; exact min_eq_right (by nlinarith)
  have h2 : min (α * Q) q = q := min_eq_right hQ
  rw [h1, h2]; ring

theorem llG_cases {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (Q : ℝ) (hQ : 0 ≤ Q) :
    (Q ≤ q ∧ llG θ α w c q Q = (w * (α * (1 - θ) + θ) - c) * Q) ∨
    (q ≤ Q ∧ α * Q ≤ q ∧ llG θ α w c q Q = θ * w * q + ((1 - θ) * w * α - c) * Q) ∨
    (q ≤ α * Q ∧ llG θ α w c q Q = w * q - c * Q) := by
  rcases le_total Q q with h | h
  · exact Or.inl ⟨h, llG_low hα hα1 hQ h⟩
  · rcases le_total (α * Q) q with h2 | h2
    · exact Or.inr (Or.inl ⟨h, h2, llG_mid hα h h2⟩)
    · exact Or.inr (Or.inr ⟨h2, llG_high hα hα1 hq.le h2⟩)

theorem llG_q {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) :
    llG θ α w c q q = (w * (α * (1 - θ) + θ) - c) * q := llG_low hα hα1 hq.le le_rfl

theorem llG_qa {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) :
    llG θ α w c q (q / α) = w * q - c * (q / α) := by
  apply llG_high hα hα1 hq.le
  have : α * (q / α) = q := by field_simp
  rw [this]

/-- key inequality used above the kink `q/α`. -/
theorem llG_top {θ α w c q Q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (hc : 0 < c)
    (hs : (1 - θ) * w * α - c < 0) (hQ : q ≤ α * Q) :
    (1 - θ) * w * q * (1 - α) < c * (Q - q) := by
  have e1 : c * q ≤ c * (α * Q) := mul_le_mul_of_nonneg_left hQ hc.le
  have e2 : (1 - θ) * w * α * (q * (1 - α)) < c * (q * (1 - α)) :=
    mul_lt_mul_of_pos_right (by linarith) (mul_pos hq (by linarith))
  have e3 : α * ((1 - θ) * w * q * (1 - α)) < α * (c * (Q - q)) := by nlinarith
  exact lt_of_mul_lt_mul_left e3 hα.le

theorem llG_A {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (hc : 0 < c)
    (hm : c < w * (α * (1 - θ) + θ))
    (hs : (1 - θ) * w * α - c < 0) (Q : ℝ) (hQ : 0 ≤ Q) (hne : Q ≠ q) :
    llG θ α w c q Q < llG θ α w c q q := by
  have hqq := llG_q (θ := θ) (w := w) (c := c) hα hα1 hq
  have hq' := llG_mid (θ := θ) (w := w) (c := c) hα (le_refl q) (Q := q) (q := q) (by nlinarith)
  rcases llG_cases (θ := θ) (w := w) (c := c) hα hα1 hq Q hQ with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · rw [h2, hqq]
    exact mul_lt_mul_of_pos_left (lt_of_le_of_ne h1 hne) (by linarith)
  · have : q < Q := lt_of_le_of_ne h1 (Ne.symm hne)
    have := mul_neg_of_neg_of_pos hs (sub_pos.2 this)
    nlinarith
  · have hqQ : q < Q := by
      by_contra hh
      push_neg at hh
      have : α * Q ≤ α * q := mul_le_mul_of_nonneg_left hh hα.le
      nlinarith
    have hk := llG_top (θ := θ) (w := w) hα hα1 hq hc hs h1
    nlinarith

theorem llG_B {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (hc : 0 < c)
    (hm : c < w * (α * (1 - θ) + θ))
    (hs : 0 < (1 - θ) * w * α - c) (Q : ℝ) (hQ : 0 ≤ Q) (hne : Q ≠ q / α) :
    llG θ α w c q Q < llG θ α w c q (q / α) := by
  have hqa : α * (q / α) = q := by field_simp
  have hqq := llG_q (θ := θ) (w := w) (c := c) hα hα1 hq
  have hq' := llG_mid (θ := θ) (w := w) (c := c) hα (le_refl q) (Q := q) (q := q) (by nlinarith)
  have hqa' := llG_mid (θ := θ) (w := w) (c := c) hα (q := q) (Q := q / α)
    (by rw [le_div_iff₀ hα]; nlinarith) (by rw [hqa])
  have hgt : q < q / α := by rw [lt_div_iff₀ hα]; nlinarith
  rcases llG_cases (θ := θ) (w := w) (c := c) hα hα1 hq Q hQ with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · have := mul_pos hs (sub_pos.2 hgt)
    have h4 : (w * (α * (1 - θ) + θ) - c) * Q ≤ (w * (α * (1 - θ) + θ) - c) * q :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  · have hle : Q ≤ q / α := by rw [le_div_iff₀ hα]; nlinarith
    have hlt : Q < q / α := lt_of_le_of_ne hle hne
    have := mul_pos hs (sub_pos.2 hlt)
    nlinarith
  · have hle : q / α ≤ Q := by rw [div_le_iff₀ hα]; nlinarith
    have hlt : q / α < Q := lt_of_le_of_ne hle (Ne.symm hne)
    have h5 := llG_high (θ := θ) (w := w) (c := c) hα hα1 hq.le (Q := q / α) (by rw [hqa])
    have := mul_pos hc (sub_pos.2 hlt)
    nlinarith

theorem llG_C {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (hc : 0 < c)
    (hm : c < w * (α * (1 - θ) + θ))
    (hs : (1 - θ) * w * α - c = 0) (Q : ℝ) (hQ : 0 ≤ Q) :
    llG θ α w c q Q ≤ llG θ α w c q q ∧
      (llG θ α w c q Q = llG θ α w c q q ↔ q ≤ Q ∧ Q ≤ q / α) := by
  have hqa : α * (q / α) = q := by field_simp
  have hqq := llG_q (θ := θ) (w := w) (c := c) hα hα1 hq
  have hq' := llG_mid (θ := θ) (w := w) (c := c) hα (le_refl q) (Q := q) (q := q) (by nlinarith)
  have hgt : q < q / α := by rw [lt_div_iff₀ hα]; nlinarith
  have hw : (1 - θ) * w * q = c * (q / α) := by
    have : c = (1 - θ) * w * α := by linarith
    rw [this]; field_simp
  rcases llG_cases (θ := θ) (w := w) (c := c) hα hα1 hq Q hQ with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · rcases eq_or_lt_of_le h1 with e | e
    · subst e
      refine ⟨le_rfl, ⟨fun _ => ⟨le_rfl, hgt.le⟩, fun _ => rfl⟩⟩
    · have h4 : (w * (α * (1 - θ) + θ) - c) * Q < (w * (α * (1 - θ) + θ) - c) * q :=
        mul_lt_mul_of_pos_left e (by linarith)
      refine ⟨by rw [h2, hqq]; exact h4.le, ⟨fun h => ?_, fun h => ?_⟩⟩
      · rw [h2, hqq] at h; exact absurd h h4.ne
      · exact absurd (lt_of_lt_of_le e h.1) (lt_irrefl _)
  · have hle : Q ≤ q / α := by rw [le_div_iff₀ hα]; nlinarith
    have : llG θ α w c q Q = llG θ α w c q q := by rw [h3, hq', hs]; ring
    exact ⟨this.le, ⟨fun _ => ⟨h1, hle⟩, fun _ => this⟩⟩
  · have hle : q / α ≤ Q := by rw [div_le_iff₀ hα]; nlinarith
    have h5 := llG_high (θ := θ) (w := w) (c := c) hα hα1 hq.le (Q := q / α) (by rw [hqa])
    have hv : llG θ α w c q q = w * q - c * (q / α) := by
      rw [hq', hs]; nlinarith
    rcases eq_or_lt_of_le hle with e | e
    · rw [← e] at h2 ⊢
      refine ⟨by rw [h2, hv], ⟨fun _ => ⟨hgt.le, le_rfl⟩, fun _ => by rw [h2, hv]⟩⟩
    · have := mul_pos hc (sub_pos.2 e)
      refine ⟨by rw [h2, hv]; nlinarith, ⟨fun h => ?_, fun h => ?_⟩⟩
      · rw [h2, hv] at h; nlinarith
      · exact absurd (lt_of_lt_of_le e h.2) (lt_irrefl _)

theorem llG_max1 {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (hc : 0 < c)
    (hm : c < w * (α * (1 - θ) + θ)) (hs : (1 - θ) * w * α - c < 0) (Q : ℝ) :
    (0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' → llG θ α w c q Q' ≤ llG θ α w c q Q) ↔ Q = q := by
  constructor
  · rintro ⟨hQ, hmax⟩
    by_contra hne
    have := llG_A hα hα1 hq hc hm hs Q hQ hne
    have h2 := hmax q hq.le
    linarith
  · rintro rfl
    refine ⟨hq.le, fun Q' hQ' => ?_⟩
    rcases eq_or_ne Q' Q with h | h
    · rw [h]
    · exact (llG_A hα hα1 hq hc hm hs Q' hQ' h).le

theorem llG_max2 {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (hc : 0 < c)
    (hm : c < w * (α * (1 - θ) + θ)) (hs : 0 < (1 - θ) * w * α - c) (Q : ℝ) :
    (0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' → llG θ α w c q Q' ≤ llG θ α w c q Q) ↔ Q = q / α := by
  have hqa : 0 ≤ q / α := by positivity
  constructor
  · rintro ⟨hQ, hmax⟩
    by_contra hne
    have := llG_B hα hα1 hq hc hm hs Q hQ hne
    have h2 := hmax (q / α) hqa
    linarith
  · rintro rfl
    refine ⟨hqa, fun Q' hQ' => ?_⟩
    rcases eq_or_ne Q' (q / α) with h | h
    · rw [h]
    · exact (llG_B hα hα1 hq hc hm hs Q' hQ' h).le

theorem llG_max3 {θ α w c q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) (hc : 0 < c)
    (hm : c < w * (α * (1 - θ) + θ)) (hs : (1 - θ) * w * α - c = 0) (Q : ℝ) (hQ : 0 ≤ Q) :
    (∀ Q' : ℝ, 0 ≤ Q' → llG θ α w c q Q' ≤ llG θ α w c q Q) ↔ (q ≤ Q ∧ Q ≤ q / α) := by
  have hqa : 0 ≤ q / α := by positivity
  constructor
  · intro hmax
    have h1 := hmax q hq.le
    have := (llG_C hα hα1 hq hc hm hs Q hQ)
    exact this.2.1 (le_antisymm this.1 h1)
  · intro hin Q' hQ'
    have h1 := (llG_C hα hα1 hq hc hm hs Q' hQ').1
    have h2 := (llG_C hα hα1 hq hc hm hs Q hQ).2.2 hin
    linarith

theorem solution (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (hcμ : c < P.a * μ P / P.b)
    (k : Scenario) (hk : k.byDelivery = true) (w q : ℝ) (hw₁ : c / μ P < w)
    (hw₂ : w < P.a / P.b) (hq : 0 < q) :
    (w < c / (P.α * (1 - P.θ)) →
      {Q : ℝ | 0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q} = {q} ∧
      delivered 1 q q = q ∧ delivered P.α q q = P.α * q) ∧
    (c / (P.α * (1 - P.θ)) < w →
      {Q : ℝ | 0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q} = {q / P.α} ∧
      delivered 1 (q / P.α) q = q ∧ delivered P.α (q / P.α) q = q) := by
  obtain ⟨ha, hb, hα, hα1, hθ, hθ1⟩ := hP
  have hμ : 0 < μ P := by unfold μ; nlinarith
  have hG : ∀ Q, supplierProfit P c k w Q q = llG P.θ P.α w c q Q := by
    intro Q
    simp only [supplierProfit, E, transfer, hk, llG]
    simp
  have hm : c < w * (P.α * (1 - P.θ) + P.θ) := by
    have := (div_lt_iff₀ hμ).1 hw₁
    unfold μ at this; linarith
  have hpos : 0 < P.α * (1 - P.θ) := mul_pos hα (by linarith)
  simp only [hG]
  constructor
  · intro hlt
    have hs : (1 - P.θ) * w * P.α - c < 0 := by
      have := (lt_div_iff₀ hpos).1 hlt
      nlinarith
    refine ⟨?_, ?_, ?_⟩
    · ext Q
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact llG_max1 hα hα1 hq hc hm hs Q
    · simp [delivered]
    · simp only [delivered, one_mul]
      exact min_eq_left (by nlinarith)
  · intro hlt
    have hs : 0 < (1 - P.θ) * w * P.α - c := by
      have := (div_lt_iff₀ hpos).1 hlt
      nlinarith
    refine ⟨?_, ?_, ?_⟩
    · ext Q
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact llG_max2 hα hα1 hq hc hm hs Q
    · simp only [delivered, one_mul]
      refine min_eq_right ?_
      rw [le_div_iff₀ hα]; nlinarith
    · simp only [delivered]
      have : P.α * (q / P.α) = q := by field_simp
      rw [this, min_self]
