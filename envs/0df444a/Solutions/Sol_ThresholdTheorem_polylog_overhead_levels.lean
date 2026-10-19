-- Prove2me | solution 1 for ThresholdTheorem.polylog_overhead_levels
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:25:51.590144+00:00
-- url     : https://prove2.me/submissions/17f7b1f1-9c92-4ac2-aed2-b0570a6e7dad

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

theorem solution (c p : ℝ) (d : ℕ) (hc : 0 < c) (hp : 0 ≤ p)
    (hcp : c * p < 1) :
    ∃ A : ℝ, ∀ (g : ℕ) (ε : ℝ), 1 ≤ g → 0 < ε → ε < 1 → ∃ k : ℕ,
      g * ((c * p) ^ (2 ^ k) / c) ≤ ε ∧
        (d : ℝ) ^ k ≤ A * (Real.log (g / ε) + 1) ^ Nat.clog 2 d := by
  let q := c * p
  have hq : 0 ≤ q := mul_nonneg hc.le hp
  have ht : ∀ (g : ℕ) (ε : ℝ), 1 ≤ g → 0 < ε → ε < 1 →
      1 ≤ Real.log (g / ε) + 1 := by
    intro g ε hg hε hε1
    have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have hr : 1 ≤ (g : ℝ) / ε := (le_div_iff₀ hε).2 (by linarith)
    linarith [Real.log_nonneg hr]
  by_cases hq0 : q = 0
  · refine ⟨1, fun g ε hg hε hε1 => ⟨0, ?_, ?_⟩⟩
    · simpa [show c * p = 0 from hq0] using hε.le
    · simpa using one_le_pow₀ (ht g ε hg hε hε1) (n := Nat.clog 2 d)
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hlog : 0 < -Real.log q := neg_pos.2 (Real.log_neg hqpos hcp)
  let a := 1 + (1 + |Real.log c|) / (-Real.log q)
  have ha : 1 ≤ a := by
    dsimp [a]
    linarith [div_nonneg (show 0 ≤ 1 + |Real.log c| by positivity) hlog.le]
  have halog : 1 + |Real.log c| ≤ a * (-Real.log q) := by
    dsimp [a]
    rw [add_mul, div_mul_cancel₀ _ hlog.ne', one_mul]
    linarith
  refine ⟨(2 * a) ^ Nat.clog 2 d, ?_⟩
  intro g ε hg hε hε1
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := lt_of_lt_of_le zero_lt_one hg'
  let t := Real.log (g / ε) + 1
  have ht1 : 1 ≤ t := ht g ε hg hε hε1
  have hat : 1 ≤ a * t := one_le_mul_of_one_le_of_one_le ha ht1
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hat (show (1 : ℝ) < 2 by norm_num)
  let k := n + 1
  have hklo : a * t ≤ (2 : ℝ) ^ k := hn'.le
  have hkup : (2 : ℝ) ^ k ≤ 2 * a * t := by
    dsimp [k]
    rw [pow_succ]
    linarith
  refine ⟨k, ?_, ?_⟩
  · have hprod : t * (1 + |Real.log c|) ≤ (2 : ℝ) ^ k * (-Real.log q) := by
      calc
        t * (1 + |Real.log c|) ≤ t * (a * (-Real.log q)) :=
          mul_le_mul_of_nonneg_left halog (by linarith)
        _ = (a * t) * (-Real.log q) := by ring
        _ ≤ (2 : ℝ) ^ k * (-Real.log q) :=
          mul_le_mul_of_nonneg_right hklo hlog.le
    have hlogbound : (2 : ℝ) ^ k * Real.log q ≤ Real.log c - Real.log (g / ε) := by
      have hh := mul_nonneg (sub_nonneg.2 ht1) (abs_nonneg (Real.log c))
      dsimp [t] at hprod hh
      nlinarith [neg_abs_le (Real.log c)]
    have hrpos : 0 < (g : ℝ) / ε := div_pos hgpos hε
    have hpow : q ^ (2 ^ k) ≤ c / (g / ε) := by
      apply (Real.log_le_log_iff (pow_pos hqpos _) (div_pos hc hrpos)).1
      rw [Real.log_pow, Real.log_div hc.ne' hrpos.ne']
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlogbound
    have heq : c / (g / ε) = ε / g * c := by field_simp
    rw [heq] at hpow
    have hh := (div_le_iff₀ hc).2 hpow
    have hh' := (le_div_iff₀ hgpos).1 hh
    simpa [q, mul_comm] using hh'
  · have hd : (d : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 d := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) d
    calc
      (d : ℝ) ^ k ≤ ((2 : ℝ) ^ Nat.clog 2 d) ^ k :=
        pow_le_pow_left₀ (by positivity) hd _
      _ = ((2 : ℝ) ^ k) ^ Nat.clog 2 d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (2 * a * t) ^ Nat.clog 2 d := pow_le_pow_left₀ (by positivity) hkup _
      _ = (2 * a) ^ Nat.clog 2 d * (Real.log (g / ε) + 1) ^ Nat.clog 2 d :=
        mul_pow _ _ _
