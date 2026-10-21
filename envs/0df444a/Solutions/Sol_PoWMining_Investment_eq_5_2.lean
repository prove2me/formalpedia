-- Prove2me | solution 1 for PoWMining.Investment.eq_5_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:34:08.39061+00:00
-- url     : https://prove2.me/submissions/ddef0a45-bc68-4ade-bcb8-db2480e2bfce

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

set_option autoImplicit false
open PoWMining.Investment

theorem solution {N : ℕ} (P : InvParams N) (hP : P.Standing) (i : Fin N) :
    cost P 0 i - cost P (fun _ => betaBar P) i =
        (if 1 < P.η then (P.ct i - P.c0) / (2 * P.η) else (1 - P.η / 2) * (P.ct i - P.c0)) ∧
      betaBar P ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ b ∈ Set.Icc (0 : ℝ) 1, b ≠ betaBar P →
        cost P (fun _ => betaBar P) i < cost P (fun _ => b) i := by
  have hd : 0 < P.ct i - P.c0 := sub_pos.mpr (hP.c0_lt i)
  have hη := hP.η_nonneg
  set d := P.ct i - P.c0 with hd_def
  have h0 : cost P 0 i = P.ct i := by simp [cost]
  by_cases h1 : P.η ≤ 1
  · have hb : betaBar P = 1 := by simp [betaBar, h1]
    rw [hb]
    refine ⟨?_, ⟨by norm_num, le_rfl⟩, ?_⟩
    · rw [h0]; simp only [cost, not_lt.mpr h1, if_false]; rw [hd_def]; ring
    · intro b hb' hne
      obtain ⟨hb0, hb1⟩ := hb'
      have hlt : b < 1 := lt_of_le_of_ne hb1 hne
      simp only [cost]
      have hq : 0 < 1 - P.η * (1 + b) / 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0:ℝ) ≤ 1 + b)]
      have := mul_pos (mul_pos hd (sub_pos.mpr hlt)) hq
      show P.ct i - 1 * d + P.η * d / 2 * 1 ^ 2 < P.ct i - b * d + P.η * d / 2 * b ^ 2
      nlinarith [this]
  · have h1' : 1 < P.η := not_le.mp h1
    have hηp : 0 < P.η := by linarith
    have hb : betaBar P = 1 / P.η := by simp [betaBar, h1]
    rw [hb]
    refine ⟨?_, ⟨by positivity, ?_⟩, ?_⟩
    · rw [h0]; simp only [cost, h1', if_true]; field_simp; ring
    · rw [div_le_one hηp]; exact h1'.le
    · intro b hb' hne
      simp only [cost]
      have hsq : 0 < (b - 1 / P.η) ^ 2 := by
        have : b - 1 / P.η ≠ 0 := sub_ne_zero.mpr hne
        positivity
      have key : P.ct i - 1 / P.η * d + P.η * d / 2 * (1 / P.η) ^ 2 <
          P.ct i - b * d + P.η * d / 2 * b ^ 2 := by
        have : P.ct i - b * d + P.η * d / 2 * b ^ 2 - (P.ct i - 1 / P.η * d + P.η * d / 2 * (1 / P.η) ^ 2)
            = P.η * d / 2 * (b - 1 / P.η) ^ 2 := by field_simp; ring
        have hpos : 0 < P.η * d / 2 * (b - 1 / P.η) ^ 2 := by positivity
        linarith
      simpa using key
