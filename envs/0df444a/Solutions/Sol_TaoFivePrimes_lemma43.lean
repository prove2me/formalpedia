-- Prove2me | solution 1 for TaoFivePrimes.lemma43
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T17:06:49.547522+00:00
-- url     : https://prove2.me/submissions/df0c1a30-daff-49d4-a753-e53da2eccfc9

import Mathlib
import Theorems.Thm_TaoFivePrimes_smoothedExpSum_zero_le_sup_mul_psi
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_le
import Theorems.Thm_TaoFivePrimes_smoothedExpSum_zero_asymptotic
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large

/-!
# Tao's Lemma 4.3, with the prime-counting input discharged

Source: Terence Tao, arXiv:1201.6656v4, Section 4, equations (4.3)--(4.4).
The supremum is pointwise, as required for a sum which samples the cutoff.
The L¹ norms are written as integrals of absolute values. The smooth part is
stated at the slightly stronger closed threshold `10^8 ≤ c*x`.

The imported summation-by-parts theorem is the accepted platform proof by its
original contributor. This assembly discharges its explicit `hpsi` hypothesis
using the separately proved unconditional Chebyshev error bound.
-/

open MeasureTheory

theorem solution
    (eta : ℝ → ℝ) (q : ℕ) (x : ℝ) (hq : 1 ≤ q) (hx : 1 ≤ x)
    (hnonneg : ∀ t : ℝ, 0 ≤ eta t)
    (hbounded : BddAbove (Set.range (fun t : ℝ => |eta t|)))
    (hsupp : ∀ t : ℝ, t < 0 ∨ 1 < t → eta t = 0) :
    (‖TaoFivePrimes.smoothedExpSum eta q x 0‖ ≤
        sSup (Set.range (fun t : ℝ => |eta t|)) * Chebyshev.psi x ∧
      sSup (Set.range (fun t : ℝ => |eta t|)) * Chebyshev.psi x ≤
        1.04 * sSup (Set.range (fun t : ℝ => |eta t|)) * x) ∧
    (∀ c : ℝ, 0 < c → c ≤ 1 → ContDiff ℝ (⊤ : ℕ∞) eta →
      (∀ t : ℝ, t < c ∨ 1 < t → eta t = 0) → (10 : ℝ) ^ 8 ≤ c * x →
      ‖TaoFivePrimes.smoothedExpSum eta 1 x 0 -
        (((∫ t : ℝ, |eta t|) * x : ℝ) : ℂ)‖ ≤
        1 / (40 * Real.log (c * x)) * (∫ t : ℝ, |deriv eta t|) * x) := by
  have hM : ∀ t : ℝ, |eta t| ≤ sSup (Set.range (fun t : ℝ => |eta t|)) := by
    intro t
    exact le_csSup hbounded (Set.mem_range_self t)
  have hM0 : 0 ≤ sSup (Set.range (fun t : ℝ => |eta t|)) :=
    le_trans (abs_nonneg (eta 0)) (hM 0)
  have hx0 : 0 < x := by linarith only [hx]
  constructor
  · constructor
    · exact TaoFivePrimes.smoothedExpSum_zero_le_sup_mul_psi eta
        (sSup (Set.range (fun t : ℝ => |eta t|))) q x hx hM
        (fun t ht => hsupp t (Or.inr ht))
    · calc
        sSup (Set.range (fun t : ℝ => |eta t|)) * Chebyshev.psi x ≤
            sSup (Set.range (fun t : ℝ => |eta t|)) * (1.04 * x) :=
          mul_le_mul_of_nonneg_left (TaoFivePrimes.rosser_schoenfeld_psi_le x hx0) hM0
        _ = 1.04 * sSup (Set.range (fun t : ℝ => |eta t|)) * x := by ring
  · intro c hc0 hc1 hsm hsuppc hcx
    have hcx1 : 1 < c * x := by norm_num at hcx ⊢; linarith only [hcx]
    have hcx0 : 0 < c * x := lt_trans zero_lt_one hcx1
    have hlog0 : 0 < Real.log (c * x) := Real.log_pos hcx1
    have hpsi : ∀ y : ℝ, c * x ≤ y → y ≤ x →
        |Chebyshev.psi y - y| ≤ y / (40 * Real.log (c * x)) := by
      intro y hy _
      have hy0 : 0 ≤ y := le_trans (le_of_lt hcx0) hy
      have hlog : Real.log (c * x) ≤ Real.log y := Real.log_le_log hcx0 hy
      exact (TaoFivePrimes.schoenfeld_psi_error_large y (le_trans hcx hy)).trans
        (div_le_div_of_nonneg_left hy0 (by positivity)
          (mul_le_mul_of_nonneg_left hlog (by norm_num)))
    have hmass : (∫ t : ℝ, |eta t|) = ∫ t : ℝ, eta t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => abs_of_nonneg (hnonneg t))
    rw [hmass]
    exact TaoFivePrimes.smoothedExpSum_zero_asymptotic eta hsm c x hc0 hc1 hx hsuppc hcx hpsi
