-- Prove2me | solution 1 for PrimalDualPricing.Regret.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:29:54.11193+00:00
-- url     : https://prove2.me/submissions/730b7a69-36be-46d9-b2ef-1e938f80585b

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Params

set_option autoImplicit false
open PrimalDualPricing.Regret

lemma PDR_log3 : (1.05 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (0.05 : ℝ) < 1 / (1 - 0.05) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have : Real.exp (1.05 : ℝ) = Real.exp 1 * Real.exp 0.05 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  have hp := Real.exp_pos (0.05 : ℝ)
  nlinarith

lemma PDR_logn (n : ℕ) (hn : 3 ≤ n) : (1.05 : ℝ) ≤ Real.log n := by
  refine le_trans PDR_log3 ?_
  apply Real.log_le_log (by norm_num)
  exact_mod_cast hn

lemma PDR_sq (n k : ℕ) (hn : 3 ≤ n) :
    widthP n k ^ 2 = (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (Real.log n * (3 / 5 : ℝ) ^ (k - 1) / 2) := by
  have hn0 : (0 : ℝ) < n := by positivity
  unfold widthP
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  have : (-(1 / 4 : ℝ) * (1 - (3 / 5 : ℝ) ^ (k - 1)) * ((2 : ℕ) : ℝ)) =
      -(1 / 2 : ℝ) + (3 / 5 : ℝ) ^ (k - 1) / 2 := by push_cast; ring
  rw [this, Real.rpow_add hn0]
  congr 1
  rw [Real.rpow_def_of_pos hn0]
  congr 1
  ring

lemma PDR_tau (eps : ℝ) (n k : ℕ) (hn : 3 ≤ n) :
    tau eps n k = Real.exp (-(Real.log n * (3 / 5 : ℝ) ^ (k - 1) / 2)) * Real.log n ^ (1 + 15 * eps) := by
  have hn0 : (0 : ℝ) < n := by positivity
  unfold tau
  rw [Real.rpow_def_of_pos hn0]
  congr 2
  ring

lemma PDR_mem (eps : ℝ) (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    (widthP n k ^ 2 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n ^ (2 + 16 * eps)) ↔
    Real.exp (Real.log n * (3 / 5 : ℝ) ^ (k - 1) / 2) ≤ Real.log n ^ (2 + 16 * eps) := by
  have hn0 : (0 : ℝ) < n := by positivity
  rw [PDR_sq n k hn]
  exact mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hn0 _)

lemma PDR_exp12 : Real.exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hp := Real.exp_pos (1 / 2 : ℝ)
  nlinarith

lemma PDR_r_bound (u : ℝ) (hu : 0 ≤ u) (m : ℕ) (hm : 3 * u + 1 ≤ (m : ℝ)) :
    (3 / 5 : ℝ) ^ m ≤ 3 / 5 * Real.exp (-(3 / 2) * u) := by
  have h35 : (0 : ℝ) < 3 / 5 := by norm_num
  have h1 : (3 / 5 : ℝ) ^ m = (3 / 5 : ℝ) ^ (m : ℝ) := (Real.rpow_natCast _ _).symm
  have h2 : (3 / 5 : ℝ) ^ (m : ℝ) ≤ (3 / 5 : ℝ) ^ (3 * u + 1) :=
    Real.rpow_le_rpow_of_exponent_ge h35 (by norm_num) hm
  have h3 : (3 / 5 : ℝ) ^ (3 * u + 1) = 3 / 5 * (3 / 5 : ℝ) ^ (3 * u) := by
    rw [Real.rpow_add h35, Real.rpow_one]; ring
  have h4 : (3 / 5 : ℝ) ^ (3 * u) ≤ Real.exp (-(3 / 2) * u) := by
    rw [Real.rpow_def_of_pos h35]
    apply Real.exp_le_exp.2
    have hl : Real.log (3 / 5 : ℝ) ≤ -(1 / 2) := by
      have : Real.log (3 / 5 : ℝ) = -Real.log (5 / 3) := by
        rw [← Real.log_inv]; norm_num
      rw [this]
      have : (1 / 2 : ℝ) ≤ Real.log (5 / 3) := by
        rw [Real.le_log_iff_exp_le (by norm_num)]; exact PDR_exp12
      linarith
    nlinarith
  rw [h1]
  calc _ ≤ _ := h2
    _ = _ := h3
    _ ≤ 3 / 5 * Real.exp (-(3 / 2) * u) := by
      apply mul_le_mul_of_nonneg_left h4 (by norm_num)

lemma PDR_core (u r : ℝ) (hu : 1.05 ≤ u) (hr0 : 0 < r) (hr : r ≤ 3 / 5 * Real.exp (-(3 / 2) * u)) :
    Real.exp (u * r / 2) ≤ u ^ 2 := by
  have hex : 4 * u ≤ Real.exp (3 / 2 * u) := by
    have := Real.sum_le_exp_of_nonneg (x := 3 / 2 * u) (by linarith) 4
    simp [Finset.sum_range_succ, Nat.factorial] at this
    nlinarith [sq_nonneg u, mul_pos (by linarith : (0:ℝ) < u) (by linarith : (0:ℝ) < u)]
  have hneg : Real.exp (-(3 / 2) * u) = (Real.exp (3 / 2 * u))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hpos := Real.exp_pos (3 / 2 * u)
  have ht : u * Real.exp (-(3 / 2) * u) ≤ 1 / 4 := by
    rw [hneg, ← div_eq_mul_inv, div_le_iff₀ hpos]; linarith
  have hs : u * r / 2 ≤ 3 / 40 := by nlinarith [mul_le_mul_of_nonneg_left hr (by linarith : (0:ℝ) ≤ u)]
  have hs0 : 0 < u * r / 2 := by positivity
  have h1 : Real.exp (u * r / 2) < 1 / (1 - u * r / 2) :=
    Real.exp_bound_div_one_sub_of_interval' hs0 (by linarith)
  have h2 : 1 / (1 - u * r / 2) ≤ 1.1 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  nlinarith

lemma PDR_L (eps : ℝ) (heps : 0 < eps) (n : ℕ) (hn : 3 ≤ n) :
    Real.log n ^ 2 ≤ Real.log n ^ (2 + 16 * eps) := by
  have hu := PDR_logn n hn
  have : Real.log n ^ (2 : ℝ) ≤ Real.log n ^ (2 + 16 * eps) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rwa [Real.rpow_two] at this

lemma PDR_A (eps : ℝ) (heps : 0 < eps) (n : ℕ) (hn : 3 ≤ n) :
    ∃ m : ℕ, (m : ℝ) ≤ 3 * Real.log n + 2 ∧
      (1 ≤ m + 1 ∧ widthP n (m + 1) ^ 2 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n ^ (2 + 16 * eps)) := by
  have hu := PDR_logn n hn
  set u := Real.log n with hu_def
  refine ⟨⌊3 * u⌋₊ + 2, ?_, by omega, ?_⟩
  · have := Nat.floor_le (by linarith : (0:ℝ) ≤ 3 * u)
    push_cast; linarith
  · rw [PDR_mem eps n hn, Nat.add_sub_cancel]
    have hm : 3 * u + 1 ≤ ((⌊3 * u⌋₊ + 2 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (3 * u); push_cast; linarith
    have hr := PDR_r_bound u (by linarith) _ hm
    have hr0 : (0:ℝ) < (3 / 5 : ℝ) ^ (⌊3 * u⌋₊ + 2) := by positivity
    exact le_trans (PDR_core u _ hu hr0 hr) (PDR_L eps heps n hn)

lemma PDR_B (eps : ℝ) (heps : 0 < eps) (n : ℕ) (hn : 3 ≤ n) (h2 : Real.log n ≤ 2) :
    (1 ≤ 5 ∧ widthP n 5 ^ 2 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n ^ (2 + 16 * eps)) := by
  have hu := PDR_logn n hn
  set u := Real.log n with hu_def
  refine ⟨by norm_num, ?_⟩
  rw [PDR_mem eps n hn]
  refine le_trans ?_ (PDR_L eps heps n hn)
  have hs0 : 0 < u * (3 / 5 : ℝ) ^ (5 - 1) / 2 := by positivity
  have hs : u * (3 / 5 : ℝ) ^ (5 - 1) / 2 ≤ 0.13 := by norm_num; linarith
  have h1 : Real.exp (u * (3 / 5 : ℝ) ^ (5 - 1) / 2) < 1 / (1 - u * (3 / 5 : ℝ) ^ (5 - 1) / 2) :=
    Real.exp_bound_div_one_sub_of_interval' hs0 (by linarith)
  have h3 : 1 / (1 - u * (3 / 5 : ℝ) ^ (5 - 1) / 2) ≤ u ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 h2), sq_nonneg (u - 1.05)]
  exact (h1.trans_le h3).le

theorem solution (eps : ℝ) (heps : 0 < eps) (n : ℕ) (hn : 3 ≤ n) :
    (numPhases eps n : ℝ) ≤ 3 * Real.log n + 3 := by
  obtain ⟨m, hm, hmem⟩ := PDR_A eps heps n hn
  have : numPhases eps n ≤ m + 1 := Nat.sInf_le hmem
  have h2 : (numPhases eps n : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h2
  linarith
