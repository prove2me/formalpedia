-- Prove2me | solution 1 for TokenSignal.Asymmetry.alphaStar_mono
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:23:37.848001+00:00
-- url     : https://prove2.me/submissions/a74a6edd-eb76-4fa7-89f7-e95cc7ca521c

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model
open TokenSignal.Asymmetry

theorem solution(P : Params) (hS : P.Standing) :
    StrictMonoOn (fun μL' : ℝ => αStar { P with μL := μL' }) (Set.Iio P.μH) ∧
    StrictMonoOn (fun σ' : ℝ => αStar { P with σ := σ' }) (Set.Ioi 0) := by
  obtain ⟨hγ, hσ, hμ, hC, hI, hI2⟩ := hS
  have key : ∀ d σ γ : ℝ, 0 < d → 0 < σ ^ 2 * γ →
      (d + σ ^ 2 * γ - Real.sqrt (d * (d + 2 * σ ^ 2 * γ))) / (σ ^ 2 * γ)
        = 1 - 2 * d / (Real.sqrt (d * (d + 2 * σ ^ 2 * γ)) + d) := by
    intro d σ γ hd hs
    have h0 : 0 ≤ d * (d + 2 * σ ^ 2 * γ) := by nlinarith
    have hR := Real.sq_sqrt h0
    have hR0 := Real.sqrt_nonneg (d * (d + 2 * σ ^ 2 * γ))
    have hRd : 0 < Real.sqrt (d * (d + 2 * σ ^ 2 * γ)) + d := by linarith
    set R := Real.sqrt (d * (d + 2 * σ ^ 2 * γ)) with hRdef
    clear_value R
    rw [div_eq_iff hs.ne', sub_mul, div_mul_eq_mul_div, eq_sub_iff_add_eq]
    field_simp
    linear_combination (-1 : ℝ) * hR
  constructor
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    show αStar { P with μL := a } < αStar { P with μL := b }
    unfold αStar
    simp only
    have hs : 0 < P.σ ^ 2 * P.γ := by positivity
    rw [key _ _ _ (by linarith) hs, key _ _ _ (by linarith) hs]
    set A := 4 * P.μH - 4 * a with hA
    set B := 4 * P.μH - 4 * b with hB
    have hA0 : 0 < A := by linarith
    have hB0 : 0 < B := by linarith
    have hBA : B < A := by linarith
    have hA2 := Real.sq_sqrt (by nlinarith : 0 ≤ A * (A + 2 * P.σ ^ 2 * P.γ))
    have hB2 := Real.sq_sqrt (by nlinarith : 0 ≤ B * (B + 2 * P.σ ^ 2 * P.γ))
    have hRA := Real.sqrt_nonneg (A * (A + 2 * P.σ ^ 2 * P.γ))
    have hRB := Real.sqrt_nonneg (B * (B + 2 * P.σ ^ 2 * P.γ))
    have hsq : (B * Real.sqrt (A * (A + 2 * P.σ ^ 2 * P.γ))) ^ 2 < (A * Real.sqrt (B * (B + 2 * P.σ ^ 2 * P.γ))) ^ 2 := by
      rw [mul_pow, mul_pow, hA2, hB2]
      have : 0 < A * B * (2 * P.σ ^ 2 * P.γ) * (A - B) := by
        apply mul_pos (mul_pos (mul_pos hA0 hB0) (by positivity)); linarith
      nlinarith [this]
    have hlt := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    have : 2 * B / (Real.sqrt (B * (B + 2 * P.σ ^ 2 * P.γ)) + B) < 2 * A / (Real.sqrt (A * (A + 2 * P.σ ^ 2 * P.γ)) + A) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hlt]
    linarith
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    show αStar { P with σ := a } < αStar { P with σ := b }
    unfold αStar
    simp only
    have hd : 0 < 4 * P.μH - 4 * P.μL := by linarith
    have hsa : 0 < a ^ 2 * P.γ := by positivity
    have hsb : 0 < b ^ 2 * P.γ := by positivity
    rw [key _ _ _ hd hsa, key _ _ _ hd hsb]
    have hab2 : a ^ 2 * P.γ < b ^ 2 * P.γ := by
      apply mul_lt_mul_of_pos_right _ hγ; nlinarith
    have hR : Real.sqrt ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * a ^ 2 * P.γ)) < Real.sqrt ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * b ^ 2 * P.γ)) := by
      apply Real.sqrt_lt_sqrt (by nlinarith); nlinarith
    have hRa := Real.sqrt_nonneg ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * a ^ 2 * P.γ))
    have : 2 * (4 * P.μH - 4 * P.μL) / (Real.sqrt ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * b ^ 2 * P.γ)) + (4 * P.μH - 4 * P.μL)) < 2 * (4 * P.μH - 4 * P.μL) / (Real.sqrt ((4 * P.μH - 4 * P.μL) * (4 * P.μH - 4 * P.μL + 2 * a ^ 2 * P.γ)) + (4 * P.μH - 4 * P.μL)) :=
      div_lt_div_of_pos_left (by linarith) (by linarith) (by linarith)
    linarith
