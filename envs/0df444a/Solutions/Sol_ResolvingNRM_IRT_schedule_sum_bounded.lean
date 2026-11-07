-- Prove2me | solution 1 for ResolvingNRM.IRT.schedule_sum_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:58:14.038301+00:00
-- url     : https://prove2.me/submissions/1da8db4e-2b56-4cf0-a25b-ba763a8e920d

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model
import Theorems.Thm_ResolvingNRM_IRT_tau_Kirt_le_exp_one

open RLPBidPrice.Unbiased Matrix ResolvingNRM.IRT

/-- `s^6 e^{-κ s} ≤ 7!/(κ^7 s)` for `s > 0`. -/
lemma irt_sched_term_bound (κ s : ℝ) (hκ : 0 < κ) (hs : 0 < s) :
    s ^ 6 * Real.exp (-κ * s) ≤ (5040 / κ ^ 7) / s := by
  have hks : 0 ≤ κ * s := by positivity
  have h7 := Real.pow_div_factorial_le_exp _ hks 7
  have hf : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hf] at h7
  have hE : 0 < Real.exp (κ * s) := Real.exp_pos _
  rw [show -κ * s = -(κ * s) by ring, Real.exp_neg, le_div_iff₀ hs]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 5040)] at h7
  have : s ^ 6 * (Real.exp (κ * s))⁻¹ * s = s ^ 7 / Real.exp (κ * s) := by
    field_simp
  rw [this, div_le_div_iff₀ hE (by positivity)]
  have : (κ * s) ^ 7 = κ ^ 7 * s ^ 7 := by ring
  nlinarith [pow_pos hκ 7, pow_pos hs 7]

theorem solution (κ : ℝ) (hκ : 0 < κ) :
    ∃ B : ℝ, ∀ T : ℝ, 1 ≤ T →
      (∑ u ∈ Finset.range (Kirt T),
          T ^ ((5 / 6 : ℝ) ^ u) * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ u / 6))) +
        T ^ ((5 / 6 : ℝ) ^ Kirt T / 2) ≤ B := by
  set c : ℝ := 5040 / κ ^ 7 with hc
  set q : ℝ := Real.exp (-(1 / 30)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hc0 : 0 < c := by positivity
  refine ⟨c / (1 - q) + Real.exp 1, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hL
  set K := Kirt T with hK
  -- second term
  have hX : T ^ ((5 / 6 : ℝ) ^ K / 2) ≤ Real.exp 1 := by
    refine le_trans ?_ (tau_Kirt_le_exp_one T hT)
    apply Real.rpow_le_rpow_of_exponent_le hT
    have : 0 ≤ (5 / 6 : ℝ) ^ K := by positivity
    linarith
  -- each term
  have hterm : ∀ u ∈ Finset.range K,
      T ^ ((5 / 6 : ℝ) ^ u) * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ u / 6)) ≤
        c * q ^ (K - 1 - u) := by
    intro u hu
    rw [Finset.mem_range] at hu
    -- (K-1) < log L / log (6/5)
    have hlt : ((K - 1 : ℕ) : ℝ) < Real.log L / Real.log (6 / 5) := by
      have : K - 1 < K := by omega
      have hKdef : K = ⌈Real.log L / Real.log (6 / 5)⌉₊ := rfl
      rw [hKdef] at this
      exact Nat.lt_ceil.mp this
    have hl65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
    have hlogL : ((K - 1 : ℕ) : ℝ) * Real.log (6 / 5) < Real.log L := by
      rwa [lt_div_iff₀ hl65] at hlt
    have hlogL0 : 0 < Real.log L := lt_of_le_of_lt (by positivity) hlogL
    have hL0 : 0 < L := by
      have hLn : 0 ≤ L := Real.log_nonneg hT
      rcases eq_or_lt_of_le hLn with h | h
      · rw [← h] at hlogL0; simp at hlogL0
      · exact h
    have hpowL : (6 / 5 : ℝ) ^ (K - 1) < L := by
      have h1 : Real.exp (((K - 1 : ℕ) : ℝ) * Real.log (6 / 5)) < Real.exp (Real.log L) :=
        Real.exp_lt_exp.mpr hlogL
      rwa [Real.exp_log hL0, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity),
        Real.rpow_natCast] at h1
    set v := K - 1 - u with hv
    have hKv : K - 1 = u + v := by omega
    have ha : 1 + (v : ℝ) / 5 ≤ (5 / 6 : ℝ) ^ u * L := by
      have hb : 1 + (v : ℝ) * (1 / 5) ≤ (1 + 1 / 5 : ℝ) ^ v :=
        one_add_mul_le_pow (by norm_num) v
      have h2 : (6 / 5 : ℝ) ^ v = (5 / 6 : ℝ) ^ u * (6 / 5 : ℝ) ^ (K - 1) := by
        rw [hKv, pow_add, ← mul_assoc, ← mul_pow]; norm_num
      have h3 : (5 / 6 : ℝ) ^ u * (6 / 5 : ℝ) ^ (K - 1) ≤ (5 / 6 : ℝ) ^ u * L :=
        mul_le_mul_of_nonneg_left hpowL.le (by positivity)
      have : (1 + 1 / 5 : ℝ) = 6 / 5 := by norm_num
      rw [this] at hb
      linarith
    set a := (5 / 6 : ℝ) ^ u * L with ha_def
    have hτ : T ^ ((5 / 6 : ℝ) ^ u) = (Real.exp (a / 6)) ^ 6 := by
      rw [Real.rpow_def_of_pos hT0, ← Real.exp_nat_mul]
      congr 1; rw [ha_def, hL]; push_cast; ring
    have hτ6 : T ^ ((5 / 6 : ℝ) ^ u / 6) = Real.exp (a / 6) := by
      rw [Real.rpow_def_of_pos hT0]; congr 1; rw [ha_def, hL]; ring
    rw [hτ, hτ6]
    refine le_trans (irt_sched_term_bound κ _ hκ (Real.exp_pos _)) ?_
    rw [div_eq_mul_inv, ← Real.exp_neg]
    apply mul_le_mul_of_nonneg_left _ hc0.le
    rw [hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (v : ℝ) / 30 ≤ a / 6 := by linarith
    linarith
  have hsum : (∑ u ∈ Finset.range K,
      T ^ ((5 / 6 : ℝ) ^ u) * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ u / 6))) ≤ c / (1 - q) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, Finset.sum_range_reflect (fun v => q ^ v) K]
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hc0.le
    rw [← tsum_geometric_of_lt_one hq0.le hq1]
    exact Summable.sum_le_tsum _ (fun i _ => by positivity) (summable_geometric_of_lt_one hq0.le hq1)
  linarith
