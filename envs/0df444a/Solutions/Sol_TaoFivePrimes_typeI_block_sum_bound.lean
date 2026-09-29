-- Prove2me | solution 1 for TaoFivePrimes.typeI_block_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:25:38.367533+00:00
-- url     : https://prove2.me/submissions/a59d286e-9472-4fde-9a15-f909230a57de

import Mathlib

open Finset

section PartS5I
open Finset
namespace TaoS5I

/-- `log t ≥ 1 - 1/t` for positive `t`. -/
theorem one_sub_inv_le_log {t : ℝ} (ht : 0 < t) : 1 - 1 / t ≤ Real.log t := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / t by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt ht), Real.log_one] at h
  have : (1 : ℝ) / t - 1 ≥ -Real.log t := by linarith
  linarith

/-- The integral test for the harmonic-type sum `∑ 1/(4j+1)`. -/
theorem harmonic_quarter : ∀ J : ℕ,
    (∑ j ∈ Finset.range (J + 1), 1 / (4 * (j : ℝ) + 1))
      ≤ 1 + (1 / 4) * Real.log (4 * (J : ℝ) + 1) := by
  intro J
  induction J with
  | zero => simp
  | succ n ih =>
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hpos : (0 : ℝ) < 4 * (n : ℝ) + 1 := by linarith
      have hpos' : (0 : ℝ) < 4 * ((n : ℕ) + 1 : ℝ) + 1 := by linarith
      have hstep : 1 / (4 * ((n : ℝ) + 1) + 1)
          ≤ (1 / 4) * Real.log (4 * ((n : ℝ) + 1) + 1) - (1 / 4) * Real.log (4 * (n : ℝ) + 1) := by
        have hratio : (0 : ℝ) < (4 * ((n : ℝ) + 1) + 1) / (4 * (n : ℝ) + 1) := by positivity
        have hlog : Real.log ((4 * ((n : ℝ) + 1) + 1) / (4 * (n : ℝ) + 1))
            = Real.log (4 * ((n : ℝ) + 1) + 1) - Real.log (4 * (n : ℝ) + 1) :=
          Real.log_div (by linarith) (by linarith)
        have h1 := one_sub_inv_le_log hratio
        have h2 : 1 - 1 / ((4 * ((n : ℝ) + 1) + 1) / (4 * (n : ℝ) + 1))
            = 4 / (4 * ((n : ℝ) + 1) + 1) := by
          field_simp
          ring
        rw [h2, hlog] at h1
        have h3 : (4:ℝ) / (4 * ((n : ℝ) + 1) + 1) = 4 * (1 / (4 * ((n : ℝ) + 1) + 1)) := by
          ring
        rw [h3] at h1
        linarith
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ]
      rw [hcast]
      linarith [ih, hstep]

/-- **Tao, Section 5**: the block sum `∑_j x/(2jq + q/2)` arising in the Type I estimate.
The additive `4` is not present in the source's display; see the Deviation note. -/
theorem block_sum_bound (x q M : ℝ) (hx : 0 ≤ x) (hq : 0 < q)
    (J : ℕ) (hJ : (J : ℝ) ≤ M / (2 * q) - 1 / 4) :
    (∑ j ∈ Finset.range (J + 1), x / (2 * (j : ℝ) * q + q / 2))
      ≤ (x / (2 * q)) * (Real.log (2 * M / q + 4) + 4) := by
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hM : 4 * (J : ℝ) + 1 ≤ 2 * M / q := by
    have h1 : (J : ℝ) + 1 / 4 ≤ M / (2 * q) := by linarith
    have h2 : 4 * ((J : ℝ) + 1 / 4) ≤ 4 * (M / (2 * q)) := by linarith
    have h3 : 4 * (M / (2 * q)) = 2 * M / q := by field_simp; ring
    linarith [h2, h3]
  have hMpos : (0 : ℝ) < 2 * M / q := by linarith
  -- rewrite each term
  have hterm : ∀ j ∈ Finset.range (J + 1),
      x / (2 * (j : ℝ) * q + q / 2) = (x / q) * (1 / (2 * (j : ℝ) + 1 / 2)) := by
    intro j _
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hden : 2 * (j : ℝ) * q + q / 2 = q * (2 * (j : ℝ) + 1 / 2) := by ring
    rw [hden]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hhalf : ∀ j ∈ Finset.range (J + 1),
      (1 : ℝ) / (2 * (j : ℝ) + 1 / 2) = 2 * (1 / (4 * (j : ℝ) + 1)) := by
    intro j _
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have h1 : (0:ℝ) < 2 * (j : ℝ) + 1 / 2 := by linarith
    have h2 : (0:ℝ) < 4 * (j : ℝ) + 1 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hhalf, ← Finset.mul_sum]
  have hh := harmonic_quarter J
  have hlogmono : Real.log (4 * (J : ℝ) + 1) ≤ Real.log (2 * M / q + 4) := by
    apply Real.log_le_log (by linarith)
    linarith
  have hxq : (0 : ℝ) ≤ x / q := by positivity
  have hkey : (2 : ℝ) * (∑ j ∈ Finset.range (J + 1), 1 / (4 * (j : ℝ) + 1))
      ≤ (1 / 2) * (Real.log (2 * M / q + 4) + 4) := by
    linarith [hh, hlogmono]
  have hfinal : (x / q) * ((2 : ℝ) * ∑ j ∈ Finset.range (J + 1), 1 / (4 * (j : ℝ) + 1))
      ≤ (x / q) * ((1 / 2) * (Real.log (2 * M / q + 4) + 4)) :=
    mul_le_mul_of_nonneg_left hkey hxq
  have hrw : (x / q) * ((1 / 2) * (Real.log (2 * M / q + 4) + 4))
      = (x / (2 * q)) * (Real.log (2 * M / q + 4) + 4) := by
    field_simp
  linarith [hfinal, hrw]

end TaoS5I
end PartS5I

theorem solution (x q M : ℝ) (hx : 0 ≤ x) (hq : 0 < q)
    (J : ℕ) (hJ : (J : ℝ) ≤ M / (2 * q) - 1 / 4) :
    (∑ j ∈ Finset.range (J + 1), x / (2 * (j : ℝ) * q + q / 2))
      ≤ (x / (2 * q)) * (Real.log (2 * M / q + 4) + 4) :=
  TaoS5I.block_sum_bound x q M hx hq J hJ
