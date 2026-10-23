-- Prove2me | solution 1 for YieldPostpone.Payment.oa_threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:40:29.4997+00:00
-- url     : https://prove2.me/submissions/32cf501f-83c9-4ea6-8220-f2d805eaf496

import Definitions.Def_YieldPostpone_Payment_Setting

open YieldPostpone.Payment

private lemma oto_core (a b α θ s : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α)
    (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 ≤ s)
    (hμ : s ^ 2 = α * (1 - θ) + θ) :
    a * α * (s ^ 2 - α * θ - 2 * θ * s) / (b * (α + θ)) <
      (-(-(2 * α ^ 2 * a * s ^ 2 * b) +
          4 * b * s ^ 2 * (a * α - b * (a * α * (s ^ 2 - θ * s) / (b * (α + θ))))) +
        Real.sqrt ((-(2 * α ^ 2 * a * s ^ 2 * b) +
          4 * b * s ^ 2 * (a * α - b * (a * α * (s ^ 2 - θ * s) / (b * (α + θ))))) ^ 2 -
          4 * (α ^ 2 * b ^ 2) *
            (α ^ 2 * (a * s ^ 2) ^ 2 -
              4 * b * s ^ 2 * (a * α - b * (a * α * (s ^ 2 - θ * s) / (b * (α + θ)))) *
                (a * α * (s ^ 2 - θ * s) / (b * (α + θ)))))) / (2 * (α ^ 2 * b ^ 2)) ∧
    (-(-(2 * α ^ 2 * a * s ^ 2 * b) +
          4 * b * s ^ 2 * (a * α - b * (a * α * (s ^ 2 - θ * s) / (b * (α + θ))))) +
        Real.sqrt ((-(2 * α ^ 2 * a * s ^ 2 * b) +
          4 * b * s ^ 2 * (a * α - b * (a * α * (s ^ 2 - θ * s) / (b * (α + θ))))) ^ 2 -
          4 * (α ^ 2 * b ^ 2) *
            (α ^ 2 * (a * s ^ 2) ^ 2 -
              4 * b * s ^ 2 * (a * α - b * (a * α * (s ^ 2 - θ * s) / (b * (α + θ)))) *
                (a * α * (s ^ 2 - θ * s) / (b * (α + θ)))))) / (2 * (α ^ 2 * b ^ 2)) <
      a * α * (s ^ 2 - θ * s) / (b * (α + θ)) := by
  have h1α : 0 < 1 - α := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hαs2 : α < s ^ 2 := by rw [hμ]; nlinarith [mul_pos hθ0 h1α]
  have hs2_1 : s ^ 2 < 1 := by rw [hμ]; nlinarith [mul_pos h1θ h1α]
  have hs1 : s < 1 := by nlinarith
  have hspos : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hαs2; nlinarith
  have hs2s : s ^ 2 < s := by nlinarith
  have hsα : 0 < s - α := by linarith
  have hαθ : 0 < α + θ := by linarith
  -- closed forms
  have hw : a * α * (s ^ 2 - θ * s) / (b * (α + θ)) = a * α * s * (1 - s) / (b * (s - α)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (a * α * b * s) * hμ
  have hc1 : a * α * (s ^ 2 - α * θ - 2 * θ * s) / (b * (α + θ)) =
      a * α * (α + s - 2 * s ^ 2) / (b * (s - α)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (a * α * b * (α + s)) * hμ
  rw [hw, hc1]
  set w := a * α * s * (1 - s) / (b * (s - α)) with hwdef
  set c1 := a * α * (α + s - 2 * s ^ 2) / (b * (s - α)) with hc1def
  set A := α ^ 2 * b ^ 2 with hA
  set B := -(2 * α ^ 2 * a * s ^ 2 * b) + 4 * b * s ^ 2 * (a * α - b * w) with hB
  set C := α ^ 2 * (a * s ^ 2) ^ 2 - 4 * b * s ^ 2 * (a * α - b * w) * w with hC
  have hApos : 0 < A := by positivity
  clear_value w c1 A B C
  have hfw : A * w ^ 2 + B * w + C = α ^ 2 * (b * w - a * s ^ 2) ^ 2 := by
    rw [hA, hB, hC]; ring
  have hbw : b * w < a * s ^ 2 := by
    rw [hwdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
    have : α * (1 - s) < s * (s - α) := by nlinarith
    have := mul_lt_mul_of_pos_left this (mul_pos (mul_pos ha hb) hspos)
    nlinarith
  have h2AwB : 0 < 2 * A * w + B := by
    have hid : (2 * A * w + B) * (s - α) = 2 * a * b * α * s * (2 * s - α) * (s ^ 2 - α) := by
      rw [hA, hB, hwdef]; field_simp; ring
    have : 0 < (2 * A * w + B) * (s - α) := by
      rw [hid]
      have : 0 < 2 * s - α := by linarith
      have : 0 < s ^ 2 - α := by linarith
      positivity
    by_contra hcon
    push Not at hcon
    have := mul_nonpos_of_nonpos_of_nonneg hcon hsα.le
    linarith
  have hD : (2 * A * w + B) ^ 2 - (B ^ 2 - 4 * A * C) = 4 * A * (A * w ^ 2 + B * w + C) := by
    ring
  have hD2 : (2 * A * c1 + B) ^ 2 - (B ^ 2 - 4 * A * C) = 4 * A * (A * c1 ^ 2 + B * c1 + C) := by
    ring
  have hf1 : (A * c1 ^ 2 + B * c1 + C) * (s - α) =
      -(a ^ 2 * α ^ 2 * (s ^ 2 - α) ^ 2 * (α + 3 * s)) := by
    rw [hA, hB, hC, hwdef, hc1def]; field_simp; ring
  have hf1neg : A * c1 ^ 2 + B * c1 + C < 0 := by
    have : 0 < a ^ 2 * α ^ 2 * (s ^ 2 - α) ^ 2 * (α + 3 * s) := by
      have : 0 < s ^ 2 - α := by linarith
      positivity
    by_contra hcon
    push Not at hcon
    have := mul_nonneg hcon hsα.le
    linarith
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    have hlt : (2 * A * c1 + B) ^ 2 < B ^ 2 - 4 * A * C := by
      have := mul_neg_of_pos_of_neg (by linarith : (0:ℝ) < 4 * A) hf1neg
      linarith
    have : |2 * A * c1 + B| < Real.sqrt (B ^ 2 - 4 * A * C) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    have := le_abs_self (2 * A * c1 + B)
    linarith
  · rw [div_lt_iff₀ (by positivity)]
    have hpos : 0 < α ^ 2 * (b * w - a * s ^ 2) ^ 2 := by
      have : b * w - a * s ^ 2 ≠ 0 := by linarith
      positivity
    have hlt : B ^ 2 - 4 * A * C < (2 * A * w + B) ^ 2 := by
      rw [hfw] at hD
      have := mul_pos (by linarith : (0:ℝ) < 4 * A) hpos
      linarith
    have : Real.sqrt (B ^ 2 - 4 * A * C) < 2 * A * w + B := by
      rw [Real.sqrt_lt' h2AwB]; exact hlt
    linarith

theorem solution (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < cDA P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ0 : 0 ≤ P.μ := by
    show 0 ≤ P.α * (1 - P.θ) + P.θ
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs := Real.sq_sqrt hμ0
  have key := oto_core P.a P.b P.α P.θ (Real.sqrt P.μ) ha hb hα0 hα1 hθ0 hθ1
    (Real.sqrt_nonneg _) (by rw [hs]; rfl)
  rw [hs] at key
  exact key
