-- Prove2me | solution 1 for ZeroFreeBridge.norm_correction_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:26.566979+00:00
-- url     : https://prove2.me/submissions/31404984-6af7-46fb-ac48-4f2bef745e2f

import Mathlib

/- PHASE 4 (dVP frontier, BLASCHKE item (d3)): the Blaschke correction sum is O(L).

   Expanding `DlvpBlaschkeSplit.logDeriv_split_off_zeros` via `DlvpCanonicalLogDeriv.logDeriv_
   canonicalFactor`, each term splits into the monomial Herglotz contribution and a CORRECTION
   `(n u)·conj u/(R² − conj u·z)`.  The correction is bounded because its pole `R²/conj u` lies
   OUTSIDE the disk: `|R² − conj u·z| ≥ R² − ‖u‖‖z‖ ≥ R(R − ‖z‖) > 0`, so per term

     `‖(n u)·conj u/(R² − conj u·z)‖ ≤ |n u|/(R − ‖z‖)` ,

   and summing gives `‖Σ correction‖ ≤ (Σ |n u|)/(R − ‖z‖)` — a constant `O(1)` times the zero count
   `Σ|n u| = O(L)`.  Function-agnostic in `n`.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {R : ℝ} (hR : 0 < R) (n : ℂ → ℤ) (s : Finset ℂ)
    (hsupp : ∀ u ∈ s, u ∈ ball (0 : ℂ) R) {z : ℂ} (hz : ‖z‖ < R) :
    ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
      ≤ (∑ u ∈ s, |(n u : ℝ)|) / (R - ‖z‖) := by
  have hRz : 0 < R - ‖z‖ := by linarith
  have hterm : ∀ u ∈ s,
      ‖(n u : ℂ) * (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
        ≤ |(n u : ℝ)| / (R - ‖z‖) := by
    intro u hu
    have huR : ‖u‖ < R := by rw [← mem_ball_zero_iff]; exact hsupp u hu
    -- lower bound on the denominator: R² - ‖u‖‖z‖ ≥ R(R - ‖z‖) > 0.
    have hden_ge : R * (R - ‖z‖) ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by
      calc R * (R - ‖z‖) = R ^ 2 - R * ‖z‖ := by ring
        _ ≤ R ^ 2 - ‖u‖ * ‖z‖ := by nlinarith [norm_nonneg z, norm_nonneg u]
        _ = ‖((R : ℂ) ^ 2)‖ - ‖(starRingEnd ℂ) u * z‖ := by
            rw [norm_mul, RCLike.norm_conj]
            simp [Complex.norm_real, abs_of_pos hR, sq]
        _ ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := norm_sub_norm_le _ _
    have hden_pos : 0 < ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
      lt_of_lt_of_le (by positivity) hden_ge
    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_intCast]
    rw [div_le_div_iff₀ hden_pos hRz]
    calc |(n u : ℝ)| * ‖u‖ * (R - ‖z‖) ≤ |(n u : ℝ)| * R * (R - ‖z‖) := by
            apply mul_le_mul_of_nonneg_right _ hRz.le
            apply mul_le_mul_of_nonneg_left huR.le (abs_nonneg _)
      _ = |(n u : ℝ)| * (R * (R - ‖z‖)) := by ring
      _ ≤ |(n u : ℝ)| * ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
            mul_le_mul_of_nonneg_left hden_ge (abs_nonneg _)
  calc ‖∑ u ∈ s, (n u : ℂ) * (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖
      ≤ ∑ u ∈ s, ‖(n u : ℂ) * (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ u ∈ s, |(n u : ℝ)| / (R - ‖z‖) := Finset.sum_le_sum hterm
    _ = (∑ u ∈ s, |(n u : ℝ)|) / (R - ‖z‖) := by rw [Finset.sum_div]
