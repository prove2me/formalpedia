-- Prove2me | solution 1 for SumProduct.sumProduct_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:49:02.174797+00:00
-- url     : https://prove2.me/submissions/5564eea8-7ce8-4fb8-9c1f-fb94b7ccb232

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_theorem_1_2
section
open scoped NumberField
open Pointwise
namespace SumProduct
private lemma aux_add {B n c : ℝ} {d : ℕ} (hB1 : 1 ≤ B)
    (hc12 : c ≤ 1 / 2) (hn : B ^ (2 * d) ≤ n) :
    B ^ d * n ≤ n ^ (2 - c) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hbig : (1 : ℝ) ≤ B ^ (2 * d) := one_le_pow₀ hB1
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one (le_trans hbig hn)
  have hc1 : (0 : ℝ) ≤ 1 - c := by linarith
  have key : B ^ d ≤ n ^ (1 - c) := by
    have h1 : (B ^ (2 * d) : ℝ) ^ (1 - c) ≤ n ^ (1 - c) :=
      Real.rpow_le_rpow (pow_nonneg hB0 _) hn hc1
    rw [← Real.rpow_natCast B d]
    refine le_trans ?_ h1
    rw [← Real.rpow_natCast B (2 * d), ← Real.rpow_mul hB0]
    refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ 1 - 2 * c)]
  have hsplit : n ^ (2 - c) = n ^ (1 - c) * n := by
    rw [show (2 : ℝ) - c = (1 - c) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right key hn0.le
private lemma aux_mul {B n c : ℝ} {d : ℕ} (hB1 : 1 ≤ B)
    (hc0 : 0 ≤ c) (hlog : c * (3 * Real.log B) ≤ Real.log 2)
    (hn : n ≤ B ^ (3 * d)) (hn1 : 1 ≤ n) :
    n ^ 2 / 2 ^ d ≤ n ^ (2 - c) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hB3c : B ^ (3 * c) ≤ 2 := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
      Real.rpow_def_of_pos hBpos]
    refine Real.exp_le_exp.2 ?_
    nlinarith [hlog]
  have key : n ^ c ≤ (2 : ℝ) ^ d := by
    have h1 : n ^ c ≤ (B ^ (3 * d) : ℝ) ^ c := Real.rpow_le_rpow hn0.le hn hc0
    refine le_trans h1 ?_
    rw [← Real.rpow_natCast B (3 * d), ← Real.rpow_mul hB0,
      show ((3 * d : ℕ) : ℝ) * c = (3 * c) * (d : ℝ) by push_cast; ring,
      Real.rpow_mul hB0, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hB0 _) hB3c d
  have hsplit : n ^ (2 - c) = n ^ 2 / n ^ c := by
    rw [Real.rpow_sub hn0, ← Real.rpow_natCast n 2]
    norm_num
  rw [hsplit]
  gcongr
end SumProduct
end

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution (hMartinet : MartinetTotallyRealTowers) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ A : Finset ℝ, N ≤ A.card ∧
      ((max (A + A).card (A * A).card : ℕ) : ℝ) ≤ (A.card : ℝ) ^ (2 - c) := by
  obtain ⟨C₀, hC₀, H⟩ := theorem_1_2 hMartinet
  -- Enlarge the constant so that `B ≥ 2`; all the upper bounds are monotone in the constant.
  set B : ℝ := max C₀ 2 with hBdef
  have hB2 : 2 ≤ B := le_max_right _ _
  have hC₀B : C₀ ≤ B := le_max_left _ _
  have hB1 : 1 ≤ B := le_trans one_le_two hB2
  have hBpos : 0 < B := lt_of_lt_of_le two_pos hB2
  have hlogB : 0 < Real.log B := Real.log_pos (lt_of_lt_of_le one_lt_two hB2)
  -- The exponent saving.
  set c : ℝ := min (1 / 2) (Real.log 2 / (3 * Real.log B)) with hcdef
  have hc0 : 0 < c := by
    refine lt_min (by norm_num) ?_
    exact div_pos (Real.log_pos (by norm_num)) (by linarith)
  have hc12 : c ≤ 1 / 2 := min_le_left _ _
  -- `c · (3 log B) ≤ log 2`, from `c ≤ log 2 / (3 log B)`.
  have hlogc : c * (3 * Real.log B) ≤ Real.log 2 := by
    have hcr : c ≤ Real.log 2 / (3 * Real.log B) := min_le_right _ _
    have h3 : 0 < 3 * Real.log B := by linarith
    calc c * (3 * Real.log B)
        ≤ (Real.log 2 / (3 * Real.log B)) * (3 * Real.log B) :=
          mul_le_mul_of_nonneg_right hcr h3.le
      _ = Real.log 2 := by field_simp
  refine ⟨c, hc0, fun N => ?_⟩
  obtain ⟨d, hdN, hd2, HX⟩ := H N
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd2
  -- Apply the construction with `X = B²`.
  have hX1 : (1 : ℝ) ≤ B ^ 2 := by nlinarith
  obtain ⟨A, hlow, hhigh, hadd, hmul⟩ := HX (B ^ 2) hX1
  set n : ℝ := (A.card : ℝ) with hndef
  -- Rephrase the lower/upper bounds on `n` with base `B`.
  have hn2d : B ^ (2 * d) ≤ n := by rw [pow_mul]; exact hlow
  have hb3 : C₀ * B ^ 2 ≤ B ^ 3 := by
    rw [show B ^ 3 = B * B ^ 2 by ring]; exact mul_le_mul_of_nonneg_right hC₀B (sq_nonneg B)
  have hn3d : n ≤ B ^ (3 * d) := by
    calc n ≤ (C₀ * B ^ 2) ^ d := hhigh
      _ ≤ (B ^ 3) ^ d := pow_le_pow_left₀ (mul_nonneg hC₀.le (sq_nonneg B)) hb3 d
      _ = B ^ (3 * d) := by rw [← pow_mul]
  have hn1 : (1 : ℝ) ≤ n := le_trans (one_le_pow₀ hB1) hn2d
  -- The two estimates.
  have h_add : ((A + A).card : ℝ) ≤ n ^ (2 - c) := by
    calc ((A + A).card : ℝ) ≤ C₀ ^ d * n := hadd
      _ ≤ B ^ d * n := by gcongr
      _ ≤ n ^ (2 - c) := aux_add hB1 hc12 hn2d
  have h_mul : ((A * A).card : ℝ) ≤ n ^ (2 - c) := by
    calc ((A * A).card : ℝ) ≤ n ^ 2 / 2 ^ d := hmul
      _ ≤ n ^ (2 - c) := aux_mul hB1 hc0.le hlogc hn3d hn1
  refine ⟨A, ?_, ?_⟩
  · -- `N ≤ |A|`.
    have hb4 : (4 : ℝ) ≤ B ^ 2 := by nlinarith
    have h4 : ((4 : ℕ) ^ d : ℝ) ≤ n := by
      calc ((4 : ℕ) ^ d : ℝ) = (4 : ℝ) ^ d := by push_cast; ring
        _ ≤ (B ^ 2) ^ d := by gcongr
        _ ≤ n := hlow
    have h4nat : (4 : ℕ) ^ d ≤ A.card := by rw [hndef] at h4; exact_mod_cast h4
    calc N ≤ d := hdN
      _ ≤ 2 ^ d := (Nat.lt_two_pow_self).le
      _ ≤ 4 ^ d := Nat.pow_le_pow_left (by norm_num) d
      _ ≤ A.card := h4nat
  · rw [Nat.cast_max]
    exact max_le h_add h_mul
end SumProduct
