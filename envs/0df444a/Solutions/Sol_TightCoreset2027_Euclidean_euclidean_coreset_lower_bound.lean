-- Prove2me | solution 1 for TightCoreset2027.Euclidean.euclidean_coreset_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:43:42.552208+00:00
-- url     : https://prove2.me/submissions/f3b9f06d-2f83-413c-9c19-9f2911a4c588

import Theorems.Thm_TightCoreset2027_Euclidean_power_construction_obstruction
import Theorems.Thm_TightCoreset2027_Euclidean_baseline_coreset_lower_bound
import Theorems.Thm_TightCoreset2027_Euclidean_numeric_scale_selection
set_option autoImplicit false
open TightCoreset2027.Euclidean

theorem solution (z : ℝ) (hz : 1 ≤ z) :
    ∃ c : ℝ, 0 < c ∧ ∃ a b : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ d : ℕ, 1 ≤ d ∧ ∃ X : Finset (Point d),
          ∀ (S : Finset (Point d)) (w : Point d → NNReal),
            IsStrongCoreset z ε k X S w →
              c * lowerBoundScale z k ε /
                ((Real.log (2 + (k : ℝ))) ^ a * (Real.log (2 + 1 / ε)) ^ b)
                ≤ (S.card : ℝ) := by
  obtain ⟨A, hA, hconstruction⟩ := power_construction_obstruction z hz
  obtain ⟨c0, hc0, hbaseline⟩ := baseline_coreset_lower_bound z hz
  obtain ⟨c1, hc1, b, hselection⟩ := numeric_scale_selection z hz A hA
  have hmin : 0 < min c0 1 := lt_min hc0 (by norm_num)
  refine ⟨min c0 1 * c1, mul_pos hmin hc1, 0, b, ?_⟩
  intro k hk ε hε hε1
  let H := c1 * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b
  have hlog : 0 < Real.log (2 + 1 / ε) := Real.log_pos (by have := one_div_pos.mpr hε; linarith)
  have hH : 0 ≤ H := by dsimp [H, lowerBoundScale]; positivity
  have hscale : (min c0 1 * c1) * lowerBoundScale z k ε /
      ((Real.log (2 + (k : ℝ))) ^ 0 * (Real.log (2 + 1 / ε)) ^ b) = min c0 1 * H := by
    simp only [pow_zero, one_mul]
    dsimp [H]
    ring
  rcases hselection k hk ε hε hε1 with hboundary|hparameters
  · obtain ⟨d, hd, X, hX⟩ := hbaseline k hk ε hε hε1
    refine ⟨d, hd, X, ?_⟩
    intro S w hS
    rw [hscale]
    calc
      min c0 1 * H ≤ c0 * H := mul_le_mul_of_nonneg_right (min_le_left c0 1) hH
      _ ≤ c0 * ((k : ℝ) * Real.rpow ε (-2)) := mul_le_mul_of_nonneg_left hboundary hc0.le
      _ = c0 * (k : ℝ) * Real.rpow ε (-2) := by ring
      _ ≤ (S.card : ℝ) := hX S w hS
  · obtain ⟨n, m, L, q, hn, hm, hL, hq, hcode, hbudget, herror, hsize⟩ := hparameters
    obtain ⟨d, hd, X, hcard, hX⟩ := hconstruction n m L q k hn hm hL hq hcode hbudget
    have hHX : H ≤ (X.card : ℝ) / 2 := by
      rw [hcard]
      push_cast
      exact hsize
    refine ⟨d, hd, X, ?_⟩
    intro S w hS
    rw [hscale]
    calc
      min c0 1 * H ≤ H := by simpa using mul_le_mul_of_nonneg_right (min_le_right c0 1) hH
      _ ≤ (X.card : ℝ) / 2 := hHX
      _ ≤ (S.card : ℝ) := (hX ε hε hε1 herror S w hS).le
