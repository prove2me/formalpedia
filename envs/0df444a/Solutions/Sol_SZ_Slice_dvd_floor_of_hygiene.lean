-- Prove2me | solution 1 for SZ.Slice.dvd_floor_of_hygiene
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:52:37.874113+00:00
-- url     : https://prove2.me/submissions/148754dd-041f-4a63-bdc0-2ed76046ebb8

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_p_cast_pos
import Theorems.Thm_SZ_Slice_three_le_cast
import Theorems.Thm_SZ_Slice_dA_mem
import Theorems.Thm_SZ_Slice_dB_mem
import Theorems.Thm_SZ_Slice_isDigits_dA
import Theorems.Thm_SZ_Slice_isDigits_dB
import Theorems.Thm_SZ_Slice_digitReal_translate
import Theorems.Thm_P2M_SZ_Slice_digitReal_compl__fb997b0ac62f
import Theorems.Thm_SZ_digitReal_nonneg
import Theorems.Thm_SZ_dvd_floor_add_digitReal_mul_pow


set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U)
    (hA : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.dA (S.w0 j k₀) i ≤ (S.m : ℤ) - 2)
    (hB : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.e - S.dB (S.w0 j k₀) i ≤ (S.m : ℤ) - 2) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hm.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hm.le
  have hdA := isDigits_dA hw0 hw1
  have hdB := isDigits_dB hw0 hw1
  have hdY : IsDigits S.m (fun i => S.e - S.dB (S.w0 j k₀) i) :=
    { two_le := hdB.two_le
      nonneg := fun i => by have := (dB_mem hw0 hw1 i).2.2; omega
      le_sub_one := fun i => by
        have := (dB_mem hw0 hw1 i).2.1; have := S.e_le; omega }
  set x : ℝ := digitReal S.m (S.dA (S.w0 j k₀)) with hxdef
  set y'' : ℝ := digitReal S.m (S.dB (S.w0 j k₀)) with hy''def
  set y : ℝ := digitReal S.m (fun i => S.e - S.dB (S.w0 j k₀) i) with hydef
  have htrans : x + S.sq * y'' = S.sigma j k₀ := digitReal_translate S h0 h1
  have hcompl : y = S.M - y'' :=
    digitReal_compl' S hdB (fun i => (dB_mem hw0 hw1 i).2.2)
  have htrans' : x + S.sq * y''
      = ((S.p : ℝ) * (k₀ : ℝ) + S.M) * S.sq - (S.p : ℝ) * (j : ℝ) := htrans
  have hcoup : (S.p : ℝ) * (j : ℝ) + x = S.sq * ((S.p : ℝ) * (k₀ : ℝ) + y) := by
    rw [hcompl]
    linear_combination htrans'
  have hxnn : 0 ≤ x := digitReal_nonneg hdA
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hppos := S.p_cast_pos
  have hxpos : 0 < (S.p : ℝ) * (j : ℝ) + x := by nlinarith
  have hξpos : 0 < ((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) := div_pos hxpos hm
  -- the even exponents
  have heven : ∀ t : ℕ,
      S.p ∣ ⌊((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * (t + 1))⌋ := by
    intro t
    obtain ⟨i₀, hi₀, hsmall⟩ := hA t
    have hval : ((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * (t + 1))
        = (((S.p * j : ℤ) : ℝ) + x) * (S.m : ℝ) ^ t := by
      rw [pow_mul, Real.sq_sqrt hm.le]
      push_cast
      field_simp
      ring
    rw [hval]
    exact dvd_floor_add_digitReal_mul_pow hdA (dvd_mul_right S.p j)
      (fun i => (dA_mem hw0 hw1 i).1) t hi₀ hsmall
  -- the odd exponents
  have hodd : ∀ t : ℕ,
      S.p ∣ ⌊((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * t + 1)⌋ := by
    intro t
    obtain ⟨i₀, hi₀, hsmall⟩ := hB t
    have hydvd : ∀ i, S.p ∣ (S.e - S.dB (S.w0 j k₀) i) := fun i =>
      dvd_sub S.p_dvd_e (dB_mem hw0 hw1 i).1
    have hval : ((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * t + 1)
        = (((S.p * k₀ : ℤ) : ℝ) + y) * (S.m : ℝ) ^ t := by
      have hs2 : Real.sqrt S.m * Real.sqrt S.m = (S.m : ℝ) := Real.mul_self_sqrt hm.le
      have hcoup' : (S.p : ℝ) * (j : ℝ) + x
          = Real.sqrt S.m * ((S.p : ℝ) * (k₀ : ℝ) + y) := hcoup
      have hpow : Real.sqrt S.m ^ (2 * t + 1) = (S.m : ℝ) ^ t * Real.sqrt S.m := by
        rw [pow_succ, pow_mul, Real.sq_sqrt hm.le]
      rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt hm), hpow, hcoup']
      push_cast
      linear_combination (((S.p : ℝ) * (k₀ : ℝ) + y) * (S.m : ℝ) ^ t) * hs2
    rw [hval]
    exact dvd_floor_add_digitReal_mul_pow hdY (dvd_mul_right S.p k₀) hydvd t hi₀ hsmall
  refine ⟨((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ), hξpos, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨t, ht⟩ := he
    have ht1 : 1 ≤ t := by omega
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    have hn2 : n = 2 * (u + 1) := by omega
    rw [hn2]
    exact heven u
  · obtain ⟨t, rfl⟩ := ho
    exact hodd t
end SZ.Slice
