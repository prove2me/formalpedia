-- Prove2me | solution 1 for YieldPostpone.Payment.production_response
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:06:58.228547+00:00
-- url     : https://prove2.me/submissions/40179068-90d3-46c8-af99-b65d2c836e45

import Mathlib
import Definitions.Def_YieldPostpone_Payment_Setting
set_option autoImplicit false
open YieldPostpone.Payment

theorem solution (P : Params) (c w q : ℝ)
    (hP : P.Valid) (hc : costAdm P c) (hw : wAdm P c .DA w) (hq : 0 < q) :
    (w < c / (P.α * (1 - P.θ)) →
      ∀ Q : ℝ, (0 ≤ Q ∧
        ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c .DA w Q' q ≤ supplierProfit P c .DA w Q q) ↔ Q = q) ∧
    (c / (P.α * (1 - P.θ)) < w →
      ∀ Q : ℝ, (0 ≤ Q ∧
        ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c .DA w Q' q ≤ supplierProfit P c .DA w Q q) ↔
        Q = q / P.α) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  obtain ⟨hc0, -⟩ := hc
  have hμ : 0 < P.μ := by unfold Params.μ; nlinarith
  have hw1 : c / P.μ < w := by
    have := hw.1
    simpa [Scenario.byDelivery] using this
  have hw2 : c < w * P.μ := by
    rw [div_lt_iff₀ hμ] at hw1; linarith
  have hμeq : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hf : ∀ Q : ℝ, supplierProfit P c .DA w Q q =
      P.θ * (w * min Q q) + (1 - P.θ) * (w * min (P.α * Q) q) - c * Q := by
    intro Q
    simp [supplierProfit, E, transfer, Scenario.byDelivery, delivered]
  obtain ⟨r, hr⟩ : ∃ r, q = P.α * r := ⟨q / P.α, by field_simp⟩
  have hr0 : 0 < r := by
    by_contra h; push_neg at h; nlinarith
  have hqr : q / P.α = r := by rw [hr]; field_simp
  rw [hqr]
  have hαqq : q ≤ r := by rw [hr]; nlinarith
  have hwpos : 0 < w := by
    by_contra h
    push_neg at h
    nlinarith
  have hA : 0 < w * (P.α * (1 - P.θ) + P.θ) - c := by rw [← hμeq]; linarith
  have hαr : 0 < r * (1 - P.α) := mul_pos hr0 (by linarith)
  -- strict optimality at q when middle slope is negative
  have key1 : P.α * (1 - P.θ) * w < c → ∀ Q : ℝ, 0 ≤ Q → Q ≠ q →
      supplierProfit P c .DA w Q q < supplierProfit P c .DA w q q := by
    intro hs Q hQ hne
    rw [hf, hf]
    have hmq : min q q = q := min_self q
    have hαqq' : min (P.α * q) q = P.α * q := min_eq_left (by nlinarith)
    rw [hmq, hαqq']
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, min_eq_left (by nlinarith : P.α * Q ≤ q)]
      nlinarith [mul_pos (sub_pos.2 h) hA]
    · rw [min_eq_right h.le]
      rcases le_total Q r with h2 | h2
      · rw [min_eq_left (by rw [hr]; nlinarith : P.α * Q ≤ q)]
        nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hs)]
      · rw [min_eq_right (by rw [hr]; nlinarith : q ≤ P.α * Q)]
        have := mul_nonneg (sub_nonneg.2 h2) hc0.le
        have := mul_pos hαr (sub_pos.2 hs)
        rw [hr] at *
        nlinarith
  have key2 : c < P.α * (1 - P.θ) * w → ∀ Q : ℝ, 0 ≤ Q → Q ≠ r →
      supplierProfit P c .DA w Q q < supplierProfit P c .DA w r q := by
    intro hs Q hQ hne
    rw [hf, hf]
    have e1 : min r q = q := min_eq_right hαqq
    have e2 : min (P.α * r) q = q := by rw [hr]; exact min_self _
    rw [e1, e2]
    rcases lt_or_gt_of_ne hne with h | h
    · rcases le_total Q q with h2 | h2
      · rw [min_eq_left h2, min_eq_left (by nlinarith : P.α * Q ≤ q)]
        have := mul_pos hαr (sub_pos.2 hs)
        have := mul_nonneg hA.le (sub_nonneg.2 h2)
        rw [hr] at *
        nlinarith
      · rw [min_eq_right h2, min_eq_left (by rw [hr]; nlinarith : P.α * Q ≤ q)]
        nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hs)]
    · have h2 : q ≤ Q := le_trans hαqq h.le
      rw [min_eq_right h2, min_eq_right (by rw [hr]; nlinarith : q ≤ P.α * Q)]
      nlinarith [mul_pos (sub_pos.2 h) hc0]
  have hdiv : ∀ x : ℝ, x < c / (P.α * (1 - P.θ)) ↔ P.α * (1 - P.θ) * x < c := by
    intro x
    have : 0 < P.α * (1 - P.θ) := by nlinarith
    rw [lt_div_iff₀ this]; constructor <;> intro h <;> linarith
  have hdiv2 : ∀ x : ℝ, c / (P.α * (1 - P.θ)) < x ↔ c < P.α * (1 - P.θ) * x := by
    intro x
    have : 0 < P.α * (1 - P.θ) := by nlinarith
    rw [div_lt_iff₀ this]; constructor <;> intro h <;> linarith
  constructor
  · intro h Q
    have hs := (hdiv w).1 h
    constructor
    · rintro ⟨hQ, hmax⟩
      by_contra hne
      have := key1 hs Q hQ hne
      have := hmax q hq.le
      linarith
    · rintro rfl
      refine ⟨hq.le, fun Q' hQ' => ?_⟩
      by_cases h' : Q' = Q
      · rw [h']
      · exact (key1 hs Q' hQ' h').le
  · intro h Q
    have hs := (hdiv2 w).1 h
    constructor
    · rintro ⟨hQ, hmax⟩
      by_contra hne
      have := key2 hs Q hQ hne
      have := hmax r hr0.le
      linarith
    · rintro rfl
      refine ⟨hr0.le, fun Q' hQ' => ?_⟩
      by_cases h' : Q' = Q
      · rw [h']
      · exact (key2 hs Q' hQ' h').le
