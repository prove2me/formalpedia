-- Prove2me | solution 1 for PlatformLeakage.Perfect.g2_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:40:26.43998+00:00
-- url     : https://prove2.me/submissions/8c6b25be-e589-4322-9abb-da6637b9219d

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model
open PlatformLeakage.Perfect

theorem solution(P : Params) (hP : P.Std) (v : ℝ) (hv : 0 < v) :
    StrictMonoOn (fun n : ℝ => g2 P n v) (Set.Ioi 0) := by
  obtain ⟨hj, hKl, hmu, hc, hcs, hRo, hL⟩ := hP
  have hphi : 0 < P.phi := by unfold Params.phi; linarith
  have hA : 0 < P.c * P.phi := mul_pos hc hphi
  have hform : ∀ n : ℝ, 0 < n → g2 P n v = P.mu * v * (Real.sqrt (1 + n * v / (P.c * P.phi)) - 1) / (Real.sqrt (1 + n * v / (P.c * P.phi)) + 1) := by
    intro n hn
    unfold g2
    have h0 : (0:ℝ) ≤ 1 + n * v / (P.c * P.phi) := by positivity
    have hs2 := Real.sq_sqrt h0
    have hs0 := Real.sqrt_nonneg (1 + n * v / (P.c * P.phi))
    set s := Real.sqrt (1 + n * v / (P.c * P.phi))
    have hnv : P.c * P.phi * (s ^ 2 - 1) = n * v := by rw [hs2]; field_simp; ring
    clear_value s
    have hs1 : s + 1 ≠ 0 := by linarith
    have hn0 : n ≠ 0 := hn.ne'
    rw [div_mul_eq_mul_div, div_eq_div_iff hn0 hs1]
    linear_combination (P.mu * (s - 1)) * hnv
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only
  rw [hform a ha, hform b hb]
  have hsa0 := Real.sqrt_nonneg (1 + a * v / (P.c * P.phi))
  have hlt : Real.sqrt (1 + a * v / (P.c * P.phi)) < Real.sqrt (1 + b * v / (P.c * P.phi)) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    have : a * v / (P.c * P.phi) < b * v / (P.c * P.phi) := by
      apply div_lt_div_of_pos_right _ hA; nlinarith
    linarith
  set sa := Real.sqrt (1 + a * v / (P.c * P.phi))
  set sb := Real.sqrt (1 + b * v / (P.c * P.phi))
  have hmv : 0 < P.mu * v := mul_pos hmu hv
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos hmv (sub_pos.2 hlt)]
