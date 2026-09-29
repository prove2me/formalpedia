-- Prove2me | solution 3 for Schanuel.gelfond_schneider
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:39.357189+00:00
-- url     : https://prove2.me/submissions/697da0e9-c2cc-42aa-baef-edcbee2a03ec

import Mathlib
import Theorems.Thm_GelfondSchneider_common_field
import Theorems.Thm_GelfondSchneider_main_estimate

-- Gelfond–Schneider in logarithmic form, assembled from the tree: the common number field and
-- the main estimate `r ^ ((r - 3h)/2) ≤ C ^ r` for arbitrarily large `r`.
theorem solution (b l : ℂ) (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ (q : ℂ))
    (hl : IsAlgebraic ℚ (Complex.exp l)) (hl0 : l ≠ 0) :
    Transcendental ℚ (Complex.exp (b * l)) := by
  intro hγ
  obtain ⟨K, _, _, σ, α', β', γ', hα, hβ, hγ'⟩ := GelfondSchneider.common_field l b hb hl hγ
  obtain ⟨C, hC, hmain⟩ := GelfondSchneider.main_estimate K σ α' β' γ' l b hl0 hbq hα hβ hγ'
  set h := Module.finrank ℚ K
  obtain ⟨r, hNr, hr0, hr⟩ := hmain (6 * h + ⌈(C + 1) ^ 4⌉₊)
  have hr6 : (6 * h : ℝ) ≤ r := by exact_mod_cast le_trans (Nat.le_add_right _ _) hNr
  have hrC : (C + 1) ^ 4 ≤ (r : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_left _ _) hNr)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have h1 : (r : ℝ) ^ ((r : ℝ) / 4) ≤ (r : ℝ) ^ (((r : ℝ) - 3 * h) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have h2 : (C + 1) ^ (r : ℝ) ≤ (r : ℝ) ^ ((r : ℝ) / 4) := by
    calc (C + 1) ^ (r : ℝ) = ((C + 1) ^ (4 : ℝ)) ^ ((r : ℝ) / 4) := by
          rw [← Real.rpow_mul (by linarith)]; ring_nf
      _ ≤ (r : ℝ) ^ ((r : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrC) (by positivity)
  have h3 : C ^ r < (C + 1) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]; exact pow_lt_pow_left₀ (by linarith) (by linarith) hr0.ne'
  linarith

#print axioms solution
