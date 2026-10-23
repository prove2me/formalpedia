-- Prove2me | solution 1 for YieldPostpone.Payment.responsive_threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:35:25.612231+00:00
-- url     : https://prove2.me/submissions/694f5bd0-2a5b-4557-b248-01441f4a56c9

import Definitions.Def_YieldPostpone_Payment_Setting

open YieldPostpone.Payment

private lemma rto_poly (α θ : ℝ) (hα : (9 : ℝ) / 16 ≤ α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (1 - α) * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) <
      (1 + α) * ((α * (1 - θ) + θ) ^ 2 + θ -
        θ * (α * (α * (1 - θ) + θ) + (1 - α) * (1 - θ))) := by
  have hg : 0 < (1 - θ) * (3 * α + 1) * (2 * α - 1) + θ * (2 * α - 1) * (α + 2) +
      (1 - α ^ 2) * θ * (1 - θ) := by
    have h2 : 0 < 2 * α - 1 := by linarith
    have h3 : 0 < 1 - α ^ 2 := by nlinarith
    have h4 : 0 < 1 - θ := by linarith
    positivity
  have hid : (1 + α) * ((α * (1 - θ) + θ) ^ 2 + θ -
        θ * (α * (α * (1 - θ) + θ) + (1 - α) * (1 - θ))) -
      (1 - α) * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) =
      2 * α ^ 3 + (1 - α) * θ * ((1 - θ) * (3 * α + 1) * (2 * α - 1) +
        θ * (2 * α - 1) * (α + 2) + (1 - α ^ 2) * θ * (1 - θ)) := by ring
  have h1 : 0 < 1 - α := by linarith
  have hα0 : 0 < α := by linarith
  have : 0 < 2 * α ^ 3 + (1 - α) * θ * ((1 - θ) * (3 * α + 1) * (2 * α - 1) +
        θ * (2 * α - 1) * (α + 2) + (1 - α ^ 2) * θ * (1 - θ)) := by positivity
  linarith

private lemma rto_main (a b α θ : ℝ) (ha : 0 < a) (hb : 0 < b) (hα : (9 : ℝ) / 16 ≤ α)
    (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (μ : ℝ) (hμ : μ = α * (1 - θ) + θ) :
    (a / b) * α * (1 - θ) * ((1 - α) - Real.sqrt (α ^ 2 + θ / (1 - θ))) < 0 ∧
    0 < a * α * (1 - Real.sqrt (α ^ 2 * (1 - θ) + θ)) / (b * (1 + α)) ∧
    a * α * (1 - Real.sqrt (α ^ 2 * (1 - θ) + θ)) / (b * (1 + α)) <
      a * α * (1 - θ) *
        (μ ^ 2 + θ - 2 * θ * Real.sqrt (α * μ * (1 - α) * (1 - θ))) /
        (b * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)) ∧
    a * α * (1 - θ) *
        (μ ^ 2 + θ - 2 * θ * Real.sqrt (α * μ * (1 - α) * (1 - θ))) /
        (b * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)) <
      a * α * μ * (1 - θ) / (b * (μ + θ)) := by
  have hα0 : 0 < α := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hNpos : 0 < α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 := by
    positivity
  set N := α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 with hN
  set r := Real.sqrt (α * μ * (1 - α) * (1 - θ)) with hr
  set u := Real.sqrt (α ^ 2 * (1 - θ) + θ) with hu
  clear_value N r u
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : α ≤ Real.sqrt (α ^ 2 + θ / (1 - θ)) := by
      rw [Real.le_sqrt (by linarith) (by positivity)]
      have : 0 ≤ θ / (1 - θ) := by positivity
      linarith
    have hneg : (1 - α) - Real.sqrt (α ^ 2 + θ / (1 - θ)) < 0 := by linarith
    have hpos : 0 < a / b * α * (1 - θ) := by positivity
    exact mul_neg_of_pos_of_neg hpos hneg
  · have hD : α ^ 2 * (1 - θ) + θ < 1 := by
      nlinarith [mul_pos h1θ (show 0 < 1 - α ^ 2 by nlinarith)]
    have hs : u < 1 := by
      rw [hu, Real.sqrt_lt' (by norm_num)]; linarith
    have : 0 < 1 - u := by linarith
    positivity
  · have hu_ge : μ ≤ u := by
      rw [hu, Real.le_sqrt hμpos.le (by positivity), hμ]
      have : 0 ≤ θ * (1 - θ) * (1 - α) ^ 2 := by positivity
      nlinarith
    have hr_le : 2 * r ≤ α * μ + (1 - α) * (1 - θ) := by
      have : r ≤ (α * μ + (1 - α) * (1 - θ)) / 2 := by
        rw [hr, Real.sqrt_le_left]
        · nlinarith [sq_nonneg (α * μ - (1 - α) * (1 - θ))]
        · positivity
      linarith
    have hpoly := rto_poly α θ hα hα1 hθ0 hθ1
    rw [← hμ, ← hN] at hpoly
    have h1 : a * α * (1 - u) / (b * (1 + α)) ≤ a * α * (1 - μ) / (b * (1 + α)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 < a * α := by positivity
      nlinarith
    have h2 : a * α * (1 - θ) * (μ ^ 2 + θ - θ * (α * μ + (1 - α) * (1 - θ))) / (b * N) ≤
        a * α * (1 - θ) * (μ ^ 2 + θ - 2 * θ * r) / (b * N) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hk : 0 < a * α * (1 - θ) := by positivity
      have h3 : θ * (2 * r) ≤ θ * (α * μ + (1 - α) * (1 - θ)) :=
        mul_le_mul_of_nonneg_left hr_le hθ0.le
      have h4 : μ ^ 2 + θ - θ * (α * μ + (1 - α) * (1 - θ)) ≤ μ ^ 2 + θ - 2 * θ * r := by
        linarith
      exact mul_le_mul_of_nonneg_left h4 hk.le
    have h3 : a * α * (1 - μ) / (b * (1 + α)) <
        a * α * (1 - θ) * (μ ^ 2 + θ - θ * (α * μ + (1 - α) * (1 - θ))) / (b * N) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have h1μ : 1 - μ = (1 - α) * (1 - θ) := by rw [hμ]; ring
      rw [h1μ]
      have hk : 0 < a * α * (1 - θ) * b := by positivity
      have := mul_lt_mul_of_pos_left hpoly hk
      linarith
    linarith
  · have hR2 : 0 < α * μ * (1 - α) * (1 - θ) := by positivity
    have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hR2
    have hrsq : r ^ 2 = α * μ * (1 - α) * (1 - θ) := by rw [hr]; exact Real.sq_sqrt hR2.le
    set E := θ * (1 - α) * (1 - θ) * (θ ^ 2 + θ - α ^ 2 * (1 - θ) ^ 2) with hE
    clear_value E
    have hEid : (μ ^ 2 + θ) * (μ + θ) - μ * N = E := by rw [hμ, hN, hE]; ring
    have hcore : E < 2 * θ * (μ + θ) * r := by
      have hrhs : 0 < 2 * θ * (μ + θ) * r := by positivity
      by_cases hE0 : E ≤ 0
      · linarith
      · push Not at hE0
        have hK : 0 < α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) +
            α * θ * (5 - θ) - θ * (1 - θ) := by
          have h6 : 0 < α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) := by positivity
          have h7 : α * θ * (5 - θ) - θ * (1 - θ) = θ * (α * (5 - θ) - (1 - θ)) := by ring
          have h8 : 0 < θ * (α * (5 - θ) - (1 - θ)) := by
            apply mul_pos hθ0; nlinarith
          linarith
        have hG : (2 * θ * (μ + θ) * r) ^ 2 - E ^ 2 =
            θ ^ 2 * (1 - α) * (1 - θ) * N *
              (α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) +
                α * θ * (5 - θ) - θ * (1 - θ)) := by
          rw [mul_pow, hrsq, hE, hN, hμ]; ring
        have hGpos : 0 < (2 * θ * (μ + θ) * r) ^ 2 - E ^ 2 := by
          rw [hG]; positivity
        nlinarith
    have hmain : (μ ^ 2 + θ - 2 * θ * r) * (μ + θ) < μ * N := by
      have : (μ ^ 2 + θ - 2 * θ * r) * (μ + θ) = (μ ^ 2 + θ) * (μ + θ) - 2 * θ * (μ + θ) * r := by
        ring
      linarith
    rw [div_lt_div_iff₀ (mul_pos hb hNpos) (mul_pos hb (by linarith : 0 < μ + θ))]
    have hk : 0 < a * α * (1 - θ) * b := by positivity
    have := mul_lt_mul_of_pos_left hmain hk
    linarith

theorem solution (P : Params) (hP : P.Valid)
    (hα : (9 : ℝ) / 16 ≤ P.α) :
    cOR P < 0 ∧ 0 < Ctil P ∧ Ctil P < cDR1 P ∧
      cDR1 P < cDR2 P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  exact rto_main P.a P.b P.α P.θ ha hb hα hα1 hθ0 hθ1 P.μ rfl
