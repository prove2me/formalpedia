-- Prove2me | solution 1 for PlatformLeakage.Perfect.a9_i
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:29:13.520984+00:00
-- url     : https://prove2.me/submissions/9c9ebd42-64e2-4335-a9be-6c7ce3815bd3

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model
open PlatformLeakage.Perfect

theorem solution(P : Params) (hP : P.Std) (j : PType) :
    0 < g2 P 1 (max (P.v j - P.Ro) 0) - P.K j ↔ P.Ro < leakHi P j := by
  obtain ⟨hj, hKl, hmu, hc, hcs, hRo, hL⟩ := hP
  obtain ⟨hN, hv, hK⟩ := hj j
  have hphi : 0 < P.phi := by unfold Params.phi; linarith
  have hA : 0 < P.c * P.phi := mul_pos hc hphi
  unfold g2 leakHi
  set x := max (P.v j - P.Ro) 0 with hxdef
  have hx0 : 0 ≤ x := le_max_right _ _
  have hk0 := Real.sqrt_nonneg (P.K j / (P.c * P.phi * P.mu))
  have hk2 := Real.sq_sqrt (div_nonneg hK (mul_pos hA hmu).le)
  set k := Real.sqrt (P.K j / (P.c * P.phi * P.mu)) with hkdef
  have hKk : P.K j = P.c * P.phi * P.mu * k ^ 2 := by
    rw [hk2]; field_simp
  have hr2 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + 1 * x / (P.c * P.phi))
  have hr1 : 1 ≤ Real.sqrt (1 + 1 * x / (P.c * P.phi)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; have : 0 ≤ 1 * x / (P.c * P.phi) := by positivity
    linarith
  set r := Real.sqrt (1 + 1 * x / (P.c * P.phi)) with hrdef
  have hxr : x = P.c * P.phi * (r ^ 2 - 1) := by rw [hr2]; field_simp; ring
  have hg : P.c * P.mu * P.phi / 1 * (r - 1) ^ 2 - P.K j = P.c * P.phi * P.mu * ((r - 1) ^ 2 - k ^ 2) := by
    rw [hKk]; ring
  rw [hg]
  have hL2 : P.v j + P.c * P.phi * (1 - (1 + k) ^ 2) = P.v j - P.c * P.phi * (2 * k + k ^ 2) := by ring
  rw [hL2]
  clear_value r k
  clear hg hKk hr2 hk2 hL hKl
  have hAmu : 0 < P.c * P.phi * P.mu := mul_pos hA hmu
  constructor
  · intro h
    have h1 : k ^ 2 < (r - 1) ^ 2 := by
      by_contra hc'; push Not at hc'; nlinarith [mul_nonneg hAmu.le (sub_nonneg.2 hc')]
    have h2 : k < r - 1 := by
      by_contra hc'; push Not at hc'; nlinarith [mul_nonneg (sub_nonneg.2 hc') (by linarith : (0:ℝ) ≤ k + (r - 1))]
    have h4 : 2 * k + k ^ 2 < r ^ 2 - 1 := by nlinarith [mul_pos (sub_pos.2 h2) (by linarith : (0:ℝ) < k + (r - 1) + 2)]
    have h3 : P.c * P.phi * (2 * k + k ^ 2) < x := by rw [hxr]; exact mul_lt_mul_of_pos_left h4 hA
    have hT : 0 ≤ P.c * P.phi * (2 * k + k ^ 2) := mul_nonneg hA.le (by positivity)
    have hpos : 0 < x := by linarith
    have hxv : x = P.v j - P.Ro := by
      rw [hxdef] at hpos ⊢; rcases le_total (P.v j - P.Ro) 0 with h' | h'
      · rw [max_eq_right h'] at hpos; linarith
      · exact max_eq_left h'
    linarith
  · intro h
    have hT : 0 ≤ P.c * P.phi * (2 * k + k ^ 2) := mul_nonneg hA.le (by positivity)
    have hvr : P.c * P.phi * (2 * k + k ^ 2) < P.v j - P.Ro := by linarith
    have hxv : x = P.v j - P.Ro := by rw [hxdef]; exact max_eq_left (by linarith)
    have h3 : (1 + k) ^ 2 < r ^ 2 := by
      have : P.c * P.phi * (2 * k + k ^ 2) < P.c * P.phi * (r ^ 2 - 1) := by rw [← hxr, hxv]; exact hvr
      have := lt_of_mul_lt_mul_left this hA.le
      nlinarith
    have h2 : 1 + k < r := by
      by_contra hc'; push Not at hc'; nlinarith [mul_nonneg (sub_nonneg.2 hc') (by linarith : (0:ℝ) ≤ 1 + k + r)]
    have h1 : k ^ 2 < (r - 1) ^ 2 := by nlinarith [mul_pos (sub_pos.2 h2) (by linarith : (0:ℝ) < r - 1 + k)]
    exact mul_pos hAmu (by linarith)
