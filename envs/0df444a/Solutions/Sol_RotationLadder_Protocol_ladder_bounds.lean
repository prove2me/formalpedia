-- Prove2me | solution 1 for RotationLadder.Protocol.ladder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T06:02:24.700444+00:00
-- url     : https://prove2.me/submissions/6120caf8-f48a-4c3b-8cd0-163ecf60edbd

import Mathlib
import Definitions.Def_RotationLadder_Protocol_ladderProb

open RotationLadder.Protocol in
theorem solution :
    (∀ i : ℕ, 3 / 4 ≤ ladderProb i ∧ ladderProb i < Real.cos (Real.pi / 8) ^ 2 ∧
      0 < theta i ∧ theta i < Real.pi / 4) ∧
    0.853 < Real.cos (Real.pi / 8) ^ 2 ∧ Real.cos (Real.pi / 8) ^ 2 < 0.854 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hs1 : Real.sqrt 2 < 1415 / 1000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2 : 1414 / 1000 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpi := Real.pi_pos
  have hC : Real.cos (Real.pi / 8) ^ 2 = 1 / 2 + Real.sqrt 2 / 4 := by
    rw [Real.cos_sq]
    have : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
    rw [this, Real.cos_pi_div_four]; ring
  have hS : Real.sin (Real.pi / 8) ^ 2 = 1 / 2 - Real.sqrt 2 / 4 := by
    rw [Real.sin_sq, hC]; ring
  have hcpos : 0 < Real.cos (Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.tan (Real.pi / 8) := ⟨_, rfl⟩
  have ht2 : t ^ 2 * Real.cos (Real.pi / 8) ^ 2 = Real.sin (Real.pi / 8) ^ 2 := by
    rw [htdef, Real.tan_eq_sin_div_cos, div_pow, div_mul_cancel₀ _ (by positivity)]
  rw [hC, hS] at ht2
  have ht0 : 0 < t := htdef ▸ Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith)
  have ht1 : t < 1 := by nlinarith
  have hθ0 : theta 0 = Real.pi / 8 := by
    unfold theta
    rw [zero_add, zpow_one]
    exact Real.arctan_tan (by linarith) (by linarith)
  have hθ : ∀ i : ℕ, theta i = Real.arctan (t ^ (i + 1)) := by
    intro i; unfold theta
    rw [show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, htdef]
  have hcos : ∀ x : ℝ, Real.cos (Real.arctan x) ^ 2 = 1 / (1 + x ^ 2) := by
    intro x; rw [Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity)]; ring
  have hsin : ∀ x : ℝ, Real.sin (Real.arctan x) ^ 2 = x ^ 2 / (1 + x ^ 2) := by
    intro x; rw [Real.sin_arctan, div_pow, Real.sq_sqrt (by positivity)]
  refine ⟨fun i => ?_, ?_, ?_⟩
  · obtain ⟨x, hxdef⟩ : ∃ x, x = t ^ (i + 1) := ⟨_, rfl⟩
    have hx0 : 0 < x := hxdef ▸ pow_pos ht0 _
    have hxt : x ≤ t := hxdef ▸ pow_le_of_le_one ht0.le ht1.le (Nat.succ_ne_zero i)
    have hx1 : x < 1 := lt_of_le_of_lt hxt ht1
    unfold ladderProb
    rw [hθ i, hθ0, ← hxdef, hcos, hsin, hC, hS]
    obtain ⟨y, hydef⟩ : ∃ y, y = x ^ 2 := ⟨_, rfl⟩
    rw [← hydef]
    have hy0 : 0 < y := hydef ▸ pow_pos hx0 2
    have hyt : y ≤ t ^ 2 := hydef ▸ pow_le_pow_left₀ hx0.le hxt 2
    have e : 1 / (1 + y) * (1 / 2 + Real.sqrt 2 / 4) + y / (1 + y) * (1 / 2 - Real.sqrt 2 / 4)
        = ((1 / 2 + Real.sqrt 2 / 4) + y * (1 / 2 - Real.sqrt 2 / 4)) / (1 + y) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]; ring
    rw [e]
    have hy1 : 0 < 1 + y := by linarith
    have k1 : y * (2 + Real.sqrt 2) ≤ 2 - Real.sqrt 2 := by nlinarith
    have k2 : y * (2 + Real.sqrt 2) * (1 + Real.sqrt 2) ≤ Real.sqrt 2 := by
      nlinarith [mul_le_mul_of_nonneg_right k1 (show (0:ℝ) ≤ 1 + Real.sqrt 2 by linarith)]
    have k3 : 1 + y * (1 + Real.sqrt 2) ≤ Real.sqrt 2 := by
      by_contra h
      push_neg at h
      nlinarith [mul_lt_mul_of_pos_right h (show (0:ℝ) < 2 + Real.sqrt 2 by linarith)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hy1]; nlinarith
    · rw [div_lt_iff₀ hy1]; nlinarith
    · rw [← Real.arctan_zero]; exact Real.arctan_strictMono hx0
    · rw [← Real.arctan_one]; exact Real.arctan_strictMono hx1
  · rw [hC]; norm_num; linarith
  · rw [hC]; norm_num; linarith
