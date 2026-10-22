-- Prove2me | solution 1 for RevShareCoord.Effort.Linear.integrated_price
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:56:00.747304+00:00
-- url     : https://prove2.me/submissions/0fd5efe9-0363-4832-8a96-8a0a79a19009

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear



namespace RevShareCoord.Effort.Linear

theorem ip_core (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    (∀ c : ℝ, 0 < c → c < 1 → ∀ x : ℝ × ℝ,
      (x ∈ quadrant ∧ IsMaxOn (fun y : ℝ × ℝ => channelProfit τ c y.1 y.2) quadrant x) ↔
        x = (orderQty τ 1 c, effort τ 1 (orderQty τ 1 c))) ∧
    (∀ c : ℝ, 0 < c → c < 1 →
      integratedPrice τ c = (1 + c * (1 - 2 * τ ^ 2)) / (2 * (1 - τ ^ 2))) ∧
    (τ < 1 / Real.sqrt 2 → StrictMonoOn (integratedPrice τ) (Set.Ioo 0 1)) ∧
    (τ = 1 / Real.sqrt 2 → ∀ c ∈ Set.Ioo (0 : ℝ) 1, integratedPrice τ c = 1) ∧
    (1 / Real.sqrt 2 < τ → StrictAntiOn (integratedPrice τ) (Set.Ioo 0 1)) := by
  have hD : 0 < 1 - τ ^ 2 := by nlinarith
  have hq : ∀ c : ℝ, c < 1 → orderQty τ 1 c = (1 - c) / (2 * (1 - τ ^ 2)) := by
    intro c hc
    simp [orderQty, hc]
  have hprice : ∀ c : ℝ, 0 < c → c < 1 →
      integratedPrice τ c = (1 + c * (1 - 2 * τ ^ 2)) / (2 * (1 - τ ^ 2)) := by
    intro c _ hc
    unfold integratedPrice price effort
    rw [hq c hc]
    field_simp
    ring
  have hsq : ∀ s : ℝ, s = Real.sqrt 2 → 0 < s ∧ s ^ 2 = 2 := by
    intro s hs
    subst hs
    exact ⟨by positivity, Real.sq_sqrt (by norm_num)⟩
  have hlt : τ < 1 / Real.sqrt 2 ↔ 1 - 2 * τ ^ 2 > 0 := by
    obtain ⟨hs, hs2⟩ := hsq _ rfl
    rw [lt_div_iff₀ hs]
    constructor
    · intro h
      nlinarith [mul_self_nonneg (τ * Real.sqrt 2), mul_nonneg hτ0 hs.le]
    · intro h
      by_contra hn
      push_neg at hn
      nlinarith [mul_nonneg hτ0 hs.le]
  have hgt : 1 / Real.sqrt 2 < τ ↔ 1 - 2 * τ ^ 2 < 0 := by
    obtain ⟨hs, hs2⟩ := hsq _ rfl
    rw [div_lt_iff₀ hs]
    constructor
    · intro h
      nlinarith [mul_nonneg hτ0 hs.le]
    · intro h
      by_contra hn
      push_neg at hn
      nlinarith [mul_nonneg hτ0 hs.le]
  have heq : τ = 1 / Real.sqrt 2 ↔ 1 - 2 * τ ^ 2 = 0 := by
    constructor
    · intro h
      have h1 : ¬ (τ < 1 / Real.sqrt 2) := by rw [h]; exact lt_irrefl _
      have h2 : ¬ (1 / Real.sqrt 2 < τ) := by rw [h]; exact lt_irrefl _
      rw [hlt] at h1; rw [hgt] at h2
      push_neg at h1 h2
      linarith
    · intro h
      rcases lt_trichotomy τ (1 / Real.sqrt 2) with h1 | h1 | h1
      · rw [hlt] at h1; linarith
      · exact h1
      · rw [hgt] at h1; linarith
  refine ⟨?_, hprice, ?_, ?_, ?_⟩
  · intro c hc0 hc1 x
    have hqc := hq c hc1
    have hqpos : 0 < orderQty τ 1 c := by rw [hqc]; apply div_pos <;> linarith
    set q0 := orderQty τ 1 c with hq0
    have hkey : 2 * q0 * (1 - τ ^ 2) = 1 - c := by rw [hqc]; field_simp
    have hdiff : ∀ y : ℝ × ℝ, channelProfit τ c y.1 y.2 - channelProfit τ c q0 (effort τ 1 q0) =
        -((y.1 - q0) ^ 2 - 2 * τ * (y.1 - q0) * (y.2 - effort τ 1 q0) + (y.2 - effort τ 1 q0) ^ 2) := by
      intro y
      unfold channelProfit revenue price effort
      obtain ⟨a, b⟩ := y
      simp only
      have hc' : c = 1 - 2 * q0 * (1 - τ ^ 2) := by linarith
      rw [hc']
      ring
    have hQ : ∀ y : ℝ × ℝ, 0 ≤ (y.1 - q0) ^ 2 - 2 * τ * (y.1 - q0) * (y.2 - effort τ 1 q0) + (y.2 - effort τ 1 q0) ^ 2 ∧
        ((y.1 - q0) ^ 2 - 2 * τ * (y.1 - q0) * (y.2 - effort τ 1 q0) + (y.2 - effort τ 1 q0) ^ 2 = 0 → y = (q0, effort τ 1 q0)) := by
      intro y
      obtain ⟨a, b⟩ := y
      simp only
      set u := a - q0
      set v := b - effort τ 1 q0
      have e : u ^ 2 - 2 * τ * u * v + v ^ 2 = (1 - τ ^ 2) * u ^ 2 + (v - τ * u) ^ 2 := by ring
      refine ⟨by rw [e]; positivity, fun h => ?_⟩
      rw [e] at h
      have h1 : u = 0 := by
        by_contra hu
        have : 0 < (1 - τ ^ 2) * u ^ 2 := by positivity
        nlinarith [sq_nonneg (v - τ * u)]
      have h2 : v = 0 := by
        have : (v - τ * u) ^ 2 = 0 := by nlinarith [sq_nonneg (v - τ * u), sq_nonneg u]
        rw [h1] at this
        simpa using this
      have ha : a = q0 := by simp only [u] at h1; linarith
      have hb : b = effort τ 1 q0 := by simp only [v] at h2; linarith
      rw [ha, hb]
    constructor
    · rintro ⟨hx, hmax⟩
      have := hmax (show (q0, effort τ 1 q0) ∈ quadrant from ?_)
      · have h2 := hdiff x
        simp only [Set.mem_setOf_eq] at this
        have hle : channelProfit τ c q0 (effort τ 1 q0) ≤ channelProfit τ c x.1 x.2 := this
        have := (hQ x).1
        have h0 : (x.1 - q0) ^ 2 - 2 * τ * (x.1 - q0) * (x.2 - effort τ 1 q0) + (x.2 - effort τ 1 q0) ^ 2 = 0 := by linarith
        exact (hQ x).2 h0
      · unfold quadrant effort
        simp only [Set.mem_prod, Set.mem_Ici]
        constructor <;> [exact hqpos.le; positivity]
    · intro hx
      subst hx
      refine ⟨?_, ?_⟩
      · unfold quadrant effort
        simp only [Set.mem_prod, Set.mem_Ici]
        constructor <;> [exact hqpos.le; positivity]
      · intro y _
        simp only [Set.mem_setOf_eq]
        have := hdiff y
        have := (hQ y).1
        linarith
  · -- strict mono
    intro h
    have hpos := hlt.1 h
    intro a ha b hb hab
    rw [hprice a ha.1 ha.2, hprice b hb.1 hb.2, div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith
  · intro h c hc
    rw [hprice c hc.1 hc.2]
    have := heq.1 h
    rw [this]
    field_simp
    nlinarith
  · intro h
    have hneg := hgt.1 h
    intro a ha b hb hab
    rw [hprice a ha.1 ha.2, hprice b hb.1 hb.2, div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith

end RevShareCoord.Effort.Linear

open RevShareCoord.Effort.Linear


theorem solution (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    (∀ c : ℝ, 0 < c → c < 1 → ∀ x : ℝ × ℝ,
      (x ∈ quadrant ∧ IsMaxOn (fun y : ℝ × ℝ => channelProfit τ c y.1 y.2) quadrant x) ↔
        x = (orderQty τ 1 c, effort τ 1 (orderQty τ 1 c))) ∧
    (∀ c : ℝ, 0 < c → c < 1 →
      integratedPrice τ c = (1 + c * (1 - 2 * τ ^ 2)) / (2 * (1 - τ ^ 2))) ∧
    (τ < 1 / Real.sqrt 2 → StrictMonoOn (integratedPrice τ) (Set.Ioo 0 1)) ∧
    (τ = 1 / Real.sqrt 2 → ∀ c ∈ Set.Ioo (0 : ℝ) 1, integratedPrice τ c = 1) ∧
    (1 / Real.sqrt 2 < τ → StrictAntiOn (integratedPrice τ) (Set.Ioo 0 1)) := by
  exact ip_core τ hτ0 hτ1
