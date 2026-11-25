-- Prove2me | solution 1 for QH.sPsq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:07.563395+00:00
-- url     : https://prove2.me/submissions/8295cb10-982c-4017-88e7-9e7fa2c9bb50

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SumMinLeDiv
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SPsqLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sP_cN_le_log_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sP_cN_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_log_sq_div_sq_primes_tail_le
import Theorems.Thm_QH_exists_primePowerSum_le_mul_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
private theorem sum_log_primes_le_mul_log_four (Y : ℕ) :
    ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ Y * Real.log 4 := by
  rw [← Real.log_prod]
  · have h1 : ((primorial Y : ℕ) : ℝ) ≤ (4 : ℝ) ^ Y := by exact_mod_cast primorial_le_four_pow Y
    have h2 : ((primorial Y : ℕ) : ℝ) = ∏ p ∈ (range (Y + 1)).filter Nat.Prime, (p : ℝ) := by
      simp [primorial, Nat.cast_prod]
    rw [← h2, ← Real.log_pow]
    have hpos : (0 : ℝ) < (primorial Y : ℕ) := by exact_mod_cast primorial_pos Y
    exact Real.log_le_log hpos h1
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity
private theorem sum_sP_sq_large_primes_le (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ 96 * Real.log 4 * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  have hY3 : 3 ≤ Y := Nat.le_floor (by exact_mod_cast hy)
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hYlt : y < (Y : ℝ) + 1 := Nat.lt_floor_add_one y
  have hY3r : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hy0 : 0 < y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hset : ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ Y) = (Ioc Y N).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨by omega, h2⟩, hp⟩, by omega⟩
  rw [hset]
  have hterm : ∀ p ∈ (Ioc Y N).filter Nat.Prime,
      sP (cN y) N p ^ 2 ≤ 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := sP_cN_le_log_div y hy0.le N p hpp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc sP (cN y) N p ^ 2 ≤ (2 * y * Real.log p / p) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
        field_simp
        ring
  have htail := sum_log_sq_div_sq_primes_tail_le N (N - Y) Y (by omega) le_rfl
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogY : Real.log Y ≤ Real.log y := Real.log_le_log hY0 hYle
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hq : 4 * Real.log 4 * (Real.log Y + 2 * Real.log 2) / Y ≤ 24 * Real.log 4 * Real.log y / y := by
    rw [div_le_div_iff₀ hY0 hy0]
    have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hE : Real.log Y + 2 * Real.log 2 ≤ 3 * Real.log y := by linarith
    have h1 : (Real.log Y + 2 * Real.log 2) * y ≤ 3 * Real.log y * y :=
      mul_le_mul_of_nonneg_right hE hy0.le
    have h2 : 3 * Real.log y * y ≤ 3 * Real.log y * (2 * Y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 4 * Real.log 4 by positivity)
    nlinarith
  calc ∑ p ∈ (Ioc Y N).filter Nat.Prime, sP (cN y) N p ^ 2
      ≤ ∑ p ∈ (Ioc Y N).filter Nat.Prime, 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := sum_le_sum hterm
    _ = 4 * y ^ 2 * ∑ p ∈ (Ioc Y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 4 * y ^ 2 * (24 * Real.log 4 * Real.log y / y) := by
        gcongr
        exact htail.trans hq
    _ = 96 * Real.log 4 * (y * Real.log y) := by
        field_simp
        ring
private theorem sum_sP_sq_small_primes_le_of_bound (C0 : ℝ) (hC0 : 0 < C0)
    (hb : ∀ (y : ℝ), 3 ≤ y → ∀ (N p : ℕ), sP (cN y) N p ≤ C0 * Real.log y) (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ (4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4) * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  set S := ⌊Real.sqrt y⌋₊ with hSdef
  have hy0 : 0 < y := by linarith
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hsq0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hSle : (S : ℝ) ≤ Real.sqrt y := Nat.floor_le hsq0
  have hSlt : Real.sqrt y < (S : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsqsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hsq1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogsq : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
  have hlsy : Real.log y ≤ 2 * Real.sqrt y := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt y by linarith)
    rw [hlogsq] at this
    linarith
  have hsub : ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ Y) ⊆ (range (Y + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
    exact ⟨by omega, hp.1.2⟩
  have step1 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => sP (cN y) N p ^ 2) (fun p _ _ => sq_nonneg _)
  have hterm : ∀ p ∈ (range (Y + 1)).filter Nat.Prime, sP (cN y) N p ^ 2 ≤
      (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0) + 2 * C0 ^ 2 * Real.log y * Real.log p := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := hb y hy N p
    have hsqb : sP (cN y) N p ^ 2 ≤ C0 ^ 2 * Real.log y ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h0 h1 2
    have hx : 0 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by positivity
    split_ifs with hpS
    · linarith
    · have hpS' : (S : ℝ) + 1 ≤ p := by exact_mod_cast (show S + 1 ≤ p by omega)
      have hlt : Real.sqrt y < p := by linarith
      have hlog : Real.log (Real.sqrt y) ≤ Real.log p := Real.log_le_log (by linarith) hlt.le
      rw [hlogsq] at hlog
      have : C0 ^ 2 * Real.log y ^ 2 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by
        have hc : 0 ≤ C0 ^ 2 * Real.log y := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (show Real.log y ≤ 2 * Real.log p by linarith) hc]
      linarith
  have step2 := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at step2
  have hite : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0)
      ≤ ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
    rw [← sum_filter]
    have hsub2 : ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S) ⊆ range (S + 1) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      omega
    calc ∑ p ∈ ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S), C0 ^ 2 * Real.log y ^ 2
        ≤ ∑ p ∈ range (S + 1), C0 ^ 2 * Real.log y ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity)
      _ = ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  have htheta := sum_log_primes_le_mul_log_four Y
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hA : ((S : ℝ) + 1) * Real.log y ≤ 4 * y := by
    have : ((S : ℝ) + 1) * Real.log y ≤ (Real.sqrt y + 1) * (2 * Real.sqrt y) :=
      mul_le_mul (by linarith) hlsy hly (by linarith)
    nlinarith
  have hA' : ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) ≤ 4 * C0 ^ 2 * (y * Real.log y) := by
    have := mul_le_mul_of_nonneg_right hA (show 0 ≤ C0 ^ 2 * Real.log y by positivity)
    nlinarith
  have hB : 2 * C0 ^ 2 * Real.log y * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p
      ≤ 2 * C0 ^ 2 * Real.log 4 * (y * Real.log y) := by
    have h1 : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ y * Real.log 4 :=
      htheta.trans (mul_le_mul_of_nonneg_right hYle hL.le)
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C0 ^ 2 * Real.log y by positivity)
    nlinarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := by linarith
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N : ℕ,
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN y) N p ^ 2 ≤ C * y * Real.log y := by
  obtain ⟨C0, hC0, hb⟩ := exists_primePowerSum_le_mul_log
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4 + 96 * Real.log 4, by positivity, ?_⟩
  intro y hy N
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊y⌋₊)]
  have h3 := sum_sP_sq_small_primes_le_of_bound C0 hC0 hb y hy N
  have h2 := sum_sP_sq_large_primes_le y hy N
  nlinarith
end QH
