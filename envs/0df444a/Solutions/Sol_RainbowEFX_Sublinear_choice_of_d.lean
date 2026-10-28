-- Prove2me | solution 1 for RainbowEFX.Sublinear.choice_of_d
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:32:00.006988+00:00
-- url     : https://prove2.me/submissions/f74efe2c-a1dc-41e1-abbf-7cb5be5e1869

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX

open RainbowEFX.Sublinear in
theorem solution (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    let d := ⌈((n : ℝ) / ε) ^ ((1 : ℝ) / 5)⌉₊
    (1 ≤ d ∧ 2 * (n : ℝ) / (ε * d) ≤ 2 * (d : ℝ) ^ 4 ∧
      ∀ d' : ℕ, 1 ≤ d' → 2 * (n : ℝ) / (ε * d') ≤ 2 * (d' : ℝ) ^ 4 → d ≤ d') ∧
    4 * (d : ℝ) ^ 4 < 64 * ((n : ℝ) / ε) ^ ((4 : ℝ) / 5) := by
  intro d
  set x : ℝ := (n : ℝ) / ε with hx
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ hε0]; linarith
  have hx0 : 0 ≤ x := by linarith
  set y : ℝ := x ^ ((1 : ℝ) / 5) with hy
  have hy5 : y ^ 5 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy4 : x ^ ((4 : ℝ) / 5) = y ^ 4 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy1 : 1 ≤ y := by
    rw [hy]; exact Real.one_le_rpow hx1 (by norm_num)
  have hdy : y ≤ (d : ℝ) := Nat.le_ceil y
  have hdlt : (d : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  have key : ∀ d' : ℕ, 1 ≤ d' →
      (2 * (n : ℝ) / (ε * d') ≤ 2 * (d' : ℝ) ^ 4 ↔ x ≤ (d' : ℝ) ^ 5) := by
    intro d' hd'
    have : (1 : ℝ) ≤ d' := by exact_mod_cast hd'
    rw [div_le_iff₀ (by positivity), hx, div_le_iff₀ hε0]
    constructor <;> intro h <;> nlinarith
  have hd1 : 1 ≤ d := by
    have : (1 : ℝ) ≤ d := le_trans hy1 hdy
    exact_mod_cast this
  refine ⟨⟨hd1, ?_, ?_⟩, ?_⟩
  · rw [key d hd1, ← hy5]
    exact pow_le_pow_left₀ (by linarith) hdy 5
  · intro d' hd' h
    rw [key d' hd'] at h
    apply Nat.ceil_le.mpr
    by_contra hlt
    push_neg at hlt
    have := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : (5:ℕ) ≠ 0)
    linarith
  · rw [hy4]
    have h2 : (d : ℝ) < 2 * y := by linarith
    have h0 : (0 : ℝ) ≤ d := by positivity
    have := pow_lt_pow_left₀ h2 h0 (by norm_num : (4:ℕ) ≠ 0)
    nlinarith
