-- Prove2me | solution 1 for YieldPostpone.Preference.Ctil_mem
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:26:25.56298+00:00
-- url     : https://prove2.me/submissions/69d969dc-40a9-4c0b-a61d-4305e8fe59d8

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

open YieldPostpone.Preference

lemma poly_key (α θ : ℝ) (h1 : 9/16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    (1 - α) * (α^2 * (1-θ)^3 + 4*α*θ*(1-θ) + θ*(1+θ)^2) <
    ((α*(1-θ)+θ)^2 + θ - θ*((α*(1-θ)+θ)*(1-α) + α*(1-θ))) * (1+α) := by
  nlinarith [mul_pos (sub_pos.2 h2) h3, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
    mul_nonneg (sub_nonneg.2 h1) h3.le, mul_nonneg (mul_nonneg (sub_nonneg.2 h1) h3.le) (sub_pos.2 h4).le,
    mul_pos (mul_pos h3 h3) (sub_pos.2 h4), mul_pos (mul_pos h3 (sub_pos.2 h4)) (sub_pos.2 h2)]

lemma final_step (a b α θ s N D : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ1 : θ < 1) (h1s : 1 - s < (1 - α) * (1 - θ)) (hND : (1 - α) * D < N * (1 + α))
    (hD0 : 0 < D) :
    a * α * (1 - s) / (b * (1 + α)) < a * α * (1 - θ) * N / (b * D) := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hpos : 0 < a * α * b := by positivity
  have h1 : (1 - s) * D < (1 - α) * (1 - θ) * D := mul_lt_mul_of_pos_right h1s hD0
  have h2 : (1 - α) * (1 - θ) * D < (1 - θ) * N * (1 + α) := by
    have : 0 < 1 - θ := by linarith
    calc (1 - α) * (1 - θ) * D = (1 - θ) * ((1 - α) * D) := by ring
      _ < (1 - θ) * (N * (1 + α)) := mul_lt_mul_of_pos_left hND this
      _ = (1 - θ) * N * (1 + α) := by ring
  have key : (1 - s) * D < (1 - θ) * N * (1 + α) := lt_trans h1 h2
  calc a * α * (1 - s) * (b * D) = (a * α * b) * ((1 - s) * D) := by ring
    _ < (a * α * b) * ((1 - θ) * N * (1 + α)) := mul_lt_mul_of_pos_left key hpos
    _ = a * α * (1 - θ) * N * (b * (1 + α)) := by ring

theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    0 < Ctil P ∧ Ctil P < cDR1 P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  set α := P.α with hαd
  set θ := P.θ with hθd
  have hμ : μ P = α * (1 - θ) + θ := rfl
  set K := α ^ 2 * (1 - θ) + θ with hK
  have hK1 : K < 1 := by
    rw [hK]; nlinarith [mul_pos (show 0 < 1 - α ^ 2 by nlinarith) (show 0 < 1 - θ by linarith)]
  have hKα : α ^ 2 < K := by
    rw [hK]; nlinarith [mul_pos (show 0 < 1 - α ^ 2 by nlinarith) hθ0]
  set s := Real.sqrt K with hs
  have hs2 : s ^ 2 = K := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := by nlinarith
  have hsα : α < s := by nlinarith
  -- 1 - s < (1 - α)(1 - θ)
  have h1s : 1 - s < (1 - α) * (1 - θ) := by
    have e : (1 - s) * (1 + s) = (1 - α) * (1 + α) * (1 - θ) := by nlinarith
    have : (1 - s) * (1 + α) < (1 - s) * (1 + s) := by
      apply mul_lt_mul_of_pos_left (by linarith) (by linarith)
    have h' : (1 - s) * (1 + α) < (1 - α) * (1 - θ) * (1 + α) := by nlinarith
    exact lt_of_mul_lt_mul_right h' (by linarith)
  refine ⟨?_, ?_⟩
  · unfold Ctil
    rw [← hαd, ← hθd]
    apply div_pos _ (by positivity)
    apply mul_pos (mul_pos ha hα0)
    linarith
  · set X := α * μ P * (1 - α) * (1 - θ) with hX
    have hμ0 : 0 < μ P := by rw [hμ]; nlinarith
    have hu : 0 ≤ μ P * (1 - α) := by nlinarith
    have hv : 0 ≤ α * (1 - θ) := by nlinarith
    have hX0 : 0 ≤ X := by rw [hX]; nlinarith
    set t := Real.sqrt X with ht
    have ht2 : t ^ 2 = X := Real.sq_sqrt hX0
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hXuv : X = (μ P * (1 - α)) * (α * (1 - θ)) := by rw [hX]; ring
    have h2t : 2 * t ≤ μ P * (1 - α) + α * (1 - θ) := by
      have hsq : (2 * t) ^ 2 ≤ (μ P * (1 - α) + α * (1 - θ)) ^ 2 := by
        rw [mul_pow, ht2, hXuv]; nlinarith [sq_nonneg (μ P * (1 - α) - α * (1 - θ))]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    set D := α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 with hD
    have hD0 : 0 < D := by
      rw [hD]; have : 0 < 1 - θ := by linarith
      positivity
    set N := μ P ^ 2 + θ - 2 * θ * t with hN
    have hNlow : μ P ^ 2 + θ - θ * (μ P * (1 - α) + α * (1 - θ)) ≤ N := by
      rw [hN]; nlinarith [mul_le_mul_of_nonneg_left h2t hθ0.le]
    have hpk := poly_key α θ hα hα1 hθ0 hθ1
    rw [← hμ] at hpk
    have hND : (1 - α) * D < N * (1 + α) := by
      have := mul_le_mul_of_nonneg_right hNlow (show (0:ℝ) ≤ 1 + α by linarith)
      have e : D = α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 := hD
      rw [e]; linarith
    exact final_step P.a P.b α θ s N D ha hb hα0 hα1 hθ1 h1s hND hD0
