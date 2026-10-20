-- Prove2me | solution 1 for SensitivityCampaign.finite_certificate_rational
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T03:05:21.933025+00:00
-- url     : https://prove2.me/submissions/4fbeed4e-3119-48f6-b7e4-90d7236f1f97

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate

open OAI.Paper320

/-- A rational real-power comparison can be checked using natural-number powers. -/
private theorem rational_power_bound
    (A B p q : ℕ) (hq : 0 < q) (hpow : A ^ p ≤ B ^ q) :
    (A : ℝ) ^ ((p : ℝ) / (q : ℝ)) ≤ (B : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hreal : (A : ℝ) ^ p ≤ (B : ℝ) ^ q := by exact_mod_cast hpow
  have hcancel : (p : ℝ) / (q : ℝ) * (q : ℝ) = (p : ℝ) :=
    div_mul_cancel₀ _ hqR.ne'
  have hleft : ((A : ℝ) ^ ((p : ℝ) / (q : ℝ))) ^ (q : ℝ) =
      (A : ℝ) ^ p := by
    rw [← Real.rpow_mul (Nat.cast_nonneg A), hcancel, Real.rpow_natCast]
  apply (Real.rpow_le_rpow_iff
    (Real.rpow_nonneg (Nat.cast_nonneg A) _) (Nat.cast_nonneg B) hqR).mp
  rw [hleft, Real.rpow_natCast]
  exact hreal


/-- Certify an asymptotic separation using only an integer-power inequality. -/
theorem solution
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B p q : ℕ)
    (hA : 1 < A) (hB : 1 < B) (hq : 0 < q)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x)
    (hpow : A ^ p ≤ B ^ q) :
    SensitivityCampaign.AchievesExponent ((p : ℝ) / (q : ℝ)) := by
  apply SensitivityCampaign.finite_certificate f x A B
    ((p : ℝ) / (q : ℝ)) hA hB (by positivity) hs hb
  exact rational_power_bound A B p q hq hpow


