-- Prove2me | solution 1 for YieldPostpone.Interplay.threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T02:43:40.488658+00:00
-- url     : https://prove2.me/submissions/4aaeeadb-7195-4049-b7a7-30fa774273c9

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

open YieldPostpone.Interplay

lemma yp3_K_pos (α θ : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    0 < α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ := by
  have ha : 0 < α := by linarith
  have hθ' : 0 < 1 - θ := by linarith
  nlinarith [mul_pos ha h3, mul_pos (mul_pos ha ha) hθ', mul_pos (mul_pos ha h3) hθ', mul_pos h3 hθ',
    mul_pos (mul_pos ha ha) h3, mul_pos (mul_pos (mul_pos ha ha) ha) (mul_pos hθ' hθ')]

theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    cOR P < 0 ∧ cDR1 P < cDR2 P ∧ cDR2 P < cDA P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hα' : 0 < 1 - P.α := by linarith
  have hμ0 : 0 < μ P := by unfold μ; nlinarith
  have hμ1 : μ P < 1 := by unfold μ; nlinarith
  have hθμ : P.θ < μ P := by unfold μ; nlinarith
  have hμd : μ P = P.α * (1 - P.θ) + P.θ := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- c^OR < 0
    unfold cOR
    have hs : P.α < Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) := by
      rw [Real.lt_sqrt hα0.le]
      have : 0 < P.θ / (1 - P.θ) := div_pos hθ0 hθ'
      linarith
    have : (1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) < 0 := by linarith
    apply mul_neg_of_pos_of_neg _ this
    positivity
  · -- c^DR_1 < c^DR_2
    set t := Real.sqrt (P.α * μ P * (1 - P.α) * (1 - P.θ)) with htd
    have hz0 : 0 ≤ P.α * μ P * (1 - P.α) * (1 - P.θ) := by positivity
    have ht2 : t ^ 2 = P.α * μ P * (1 - P.α) * (1 - P.θ) := Real.sq_sqrt hz0
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    set D := P.α ^ 2 * (1 - P.θ) ^ 3 + 4 * P.α * P.θ * (1 - P.θ) + P.θ * (1 + P.θ) ^ 2 with hDd
    have hD : 0 < D := by positivity
    have hK := yp3_K_pos P.α P.θ hα hα1 hθ0 hθ1
    have hG : ((μ P ^ 2 + P.θ) * (μ P + P.θ) - μ P * D) ^ 2 < (2 * P.θ * t * (μ P + P.θ)) ^ 2 := by
      have e : (2 * P.θ * t * (μ P + P.θ)) ^ 2 - ((μ P ^ 2 + P.θ) * (μ P + P.θ) - μ P * D) ^ 2
          = P.θ ^ 2 * (1 - P.α) * (1 - P.θ) * D *
            (P.α^3*(1-P.θ)^2 - P.α^2*P.θ^2 - 2*P.α^2*P.θ + 3*P.α^2 - P.α*P.θ^2 + 5*P.α*P.θ + P.θ^2 - P.θ) := by
        rw [mul_pow, mul_pow, ht2, hDd, hμd]; ring
      have : 0 < P.θ ^ 2 * (1 - P.α) * (1 - P.θ) * D *
            (P.α^3*(1-P.θ)^2 - P.α^2*P.θ^2 - 2*P.α^2*P.θ + 3*P.α^2 - P.α*P.θ^2 + 5*P.α*P.θ + P.θ^2 - P.θ) := by
        positivity
      linarith
    have hL : (μ P ^ 2 + P.θ) * (μ P + P.θ) - μ P * D < 2 * P.θ * t * (μ P + P.θ) := by
      have := abs_lt_of_sq_lt_sq hG (by positivity)
      exact lt_of_le_of_lt (le_abs_self _) this
    unfold cDR1 cDR2
    rw [← htd, ← hDd, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hu : 0 < P.a * P.α * (1 - P.θ) * P.b := by positivity
    have key : (μ P ^ 2 + P.θ - 2 * P.θ * t) * (μ P + P.θ) < μ P * D := by linarith
    have := mul_lt_mul_of_pos_left key hu
    nlinarith
  · -- c^DR_2 < c^DA
    set m := Real.sqrt (μ P) with hmd
    have hm2 : m ^ 2 = μ P := Real.sq_sqrt hμ0.le
    have hm0 : 0 ≤ m := Real.sqrt_nonneg _
    have hsq : (m * (μ P + P.θ)) ^ 2 < (μ P * (1 + P.θ)) ^ 2 := by
      rw [mul_pow, hm2]
      have : 0 < 1 - μ P := by linarith
      nlinarith [mul_pos this (mul_pos hθ0 hθ0), mul_pos hθ0 (sub_pos.mpr hθμ), mul_pos this (sub_pos.mpr hθμ)]
    have hlt : m * (μ P + P.θ) < μ P * (1 + P.θ) :=
      lt_of_le_of_lt (le_abs_self _) (abs_lt_of_sq_lt_sq hsq (by positivity))
    have hin : μ P * (1 - P.θ) * (P.α + P.θ) < (μ P - P.θ * m) * (μ P + P.θ) := by
      have e : (μ P - P.θ * m) * (μ P + P.θ) - μ P * (1 - P.θ) * (P.α + P.θ)
          = P.θ * (μ P * (1 + P.θ) - m * (μ P + P.θ)) := by rw [hμd]; ring
      nlinarith [mul_pos hθ0 (sub_pos.mpr hlt)]
    unfold cDR2 cDA
    rw [← hmd, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hu : 0 < P.a * P.α * P.b := by positivity
    have := mul_lt_mul_of_pos_left hin hu
    nlinarith
