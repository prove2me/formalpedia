-- Prove2me | solution 1 for PrimalDualPricing.Regret.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:29:55.188384+00:00
-- url     : https://prove2.me/submissions/95cbc087-2fcd-4386-8c12-70ad31a9f18d

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


theorem solution (eps T : ℝ) (heps : 0 < eps) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n)
    (hn' : Real.exp ((8 / T) ^ (1 / eps)) ≤ n) :
    ∑ k ∈ Finset.Ico 1 (numPhases eps n), tau eps n k ≤ T / 2 := by
  have hu := PDR_logn n hn
  have hn0 : (0 : ℝ) < n := by positivity
  set u := Real.log n with hu_def
  have hu0 : 0 < u := by linarith
  set K := numPhases eps n with hK
  obtain ⟨m, hm, hmem⟩ := PDR_A eps heps n hn
  have hne : {k : ℕ | 1 ≤ k ∧ widthP n k ^ 2 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n ^ (2 + 16 * eps)}.Nonempty :=
    ⟨m + 1, hmem⟩
  have hKmem := Nat.sInf_mem hne
  have hK1 : 1 ≤ K := hKmem.1
  have hK4 : (K : ℝ) - 1 ≤ 4 * u := by
    by_cases h2 : 2 ≤ u
    · have : K ≤ m + 1 := Nat.sInf_le hmem
      have h2' : (K : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2'
      linarith
    · push Not at h2
      have : K ≤ 5 := Nat.sInf_le (PDR_B eps heps n hn h2.le)
      have h2' : (K : ℝ) ≤ 5 := by exact_mod_cast this
      linarith
  have hbound : ∀ k ∈ Finset.Ico 1 K, tau eps n k ≤ u ^ (-1 - eps) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hnot : k ∉ {k : ℕ | 1 ≤ k ∧ widthP n k ^ 2 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n ^ (2 + 16 * eps)} :=
      Nat.notMem_of_lt_sInf hk.2
    have hnot' : ¬ (Real.exp (u * (3 / 5 : ℝ) ^ (k - 1) / 2) ≤ u ^ (2 + 16 * eps)) := by
      intro h
      exact hnot ⟨hk.1, (PDR_mem eps n hn k).2 h⟩
    push Not at hnot'
    rw [PDR_tau eps n k hn, Real.exp_neg]
    have hL : 0 < u ^ (2 + 16 * eps) := Real.rpow_pos_of_pos hu0 _
    have h1 : (Real.exp (u * (3 / 5 : ℝ) ^ (k - 1) / 2))⁻¹ ≤ (u ^ (2 + 16 * eps))⁻¹ :=
      inv_anti₀ hL hnot'.le
    have h2 : (u ^ (2 + 16 * eps))⁻¹ * u ^ (1 + 15 * eps) = u ^ (-1 - eps) := by
      rw [← Real.rpow_neg hu0.le, ← Real.rpow_add hu0]
      congr 1; ring
    calc _ ≤ (u ^ (2 + 16 * eps))⁻¹ * u ^ (1 + 15 * eps) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu0.le _)
      _ = _ := h2
  have hsum := Finset.sum_le_card_nsmul (Finset.Ico 1 K) (fun k => tau eps n k) (u ^ (-1 - eps)) hbound
  rw [Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK1]; simp
  rw [hcast] at hsum
  -- u^ε ≥ 8/T
  have hlog : (8 / T) ^ (1 / eps) ≤ u := by
    rw [hu_def]
    exact (Real.le_log_iff_exp_le hn0).2 hn'
  have hue : 8 / T ≤ u ^ eps := by
    have h0 : 0 ≤ (8 / T) ^ (1 / eps) := Real.rpow_nonneg (by positivity) _
    have := Real.rpow_le_rpow h0 hlog heps.le
    rw [← Real.rpow_mul (by positivity)] at this
    rwa [one_div_mul_cancel heps.ne', Real.rpow_one] at this
  have huE : 0 < u ^ eps := Real.rpow_pos_of_pos hu0 _
  have hinv : (u ^ eps)⁻¹ ≤ T / 8 := by
    have : (u ^ eps)⁻¹ ≤ (8 / T)⁻¹ := inv_anti₀ (by positivity) hue
    simpa using this
  have hkey : u * u ^ (-1 - eps) = (u ^ eps)⁻¹ := by
    calc u * u ^ (-1 - eps) = u ^ ((1 : ℝ) + (-1 - eps)) := by rw [Real.rpow_add hu0, Real.rpow_one]
      _ = u ^ (-eps) := by ring_nf
      _ = (u ^ eps)⁻¹ := Real.rpow_neg hu0.le _
  have hpos : 0 ≤ u ^ (-1 - eps) := Real.rpow_nonneg hu0.le _
  calc ∑ k ∈ Finset.Ico 1 K, tau eps n k ≤ ((K : ℝ) - 1) * u ^ (-1 - eps) := hsum
    _ ≤ (4 * u) * u ^ (-1 - eps) := mul_le_mul_of_nonneg_right hK4 hpos
    _ = 4 * (u ^ eps)⁻¹ := by rw [mul_assoc, hkey]
    _ ≤ 4 * (T / 8) := by linarith
    _ = T / 2 := by ring
