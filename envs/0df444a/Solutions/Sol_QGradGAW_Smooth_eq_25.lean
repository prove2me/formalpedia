-- Prove2me | solution 1 for QGradGAW.Smooth.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:29:07.938434+00:00
-- url     : https://prove2.me/submissions/bf354b64-72a2-476e-8ee3-ad0cc1b62abe

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

set_option autoImplicit false
open QGradGAW.Smooth

lemma qg_choose_lt (m l : ℕ) (hm : 1 ≤ m) (hl : 1 ≤ l) : m.choose l < (m + l).choose l := by
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have h1 : (m + (l' + 1)).choose (l' + 1) = (m + l').choose l' + (m + l').choose (l' + 1) := by
    rw [show m + (l' + 1) = (m + l') + 1 by ring, Nat.choose_succ_succ]
  have h2 : m.choose (l' + 1) ≤ (m + l').choose (l' + 1) :=
    Nat.choose_le_choose _ (by omega)
  have h3 : 0 < (m + l').choose l' := Nat.choose_pos (by omega)
  omega

lemma qg_abs_cc (m l : ℕ) (hl : 1 ≤ l) (hlm : l ≤ m) :
    |centralCoeff m (l : ℤ)| = (1 / (l : ℝ)) * ((m.choose l : ℝ) / ((m + l).choose l : ℝ)) := by
  have hl0 : (l : ℤ) ≠ 0 := by omega
  simp only [centralCoeff, if_neg hl0, Int.natAbs_natCast]
  have hpos : (0:ℝ) < ((m + l).choose l : ℝ) := by
    have : 0 < (m + l).choose l := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hlr : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  push_cast
  have e1 : |(-1:ℝ) ^ ((l:ℤ) - 1) / (l:ℝ)| = 1 / (l:ℝ) := by
    rw [abs_div, abs_zpow]; simp [abs_of_pos hlr]
  have e2 : |(m.choose l : ℝ) / ((m + l).choose l : ℝ)| = (m.choose l : ℝ) / ((m + l).choose l : ℝ) :=
    abs_of_nonneg (by positivity)
  rw [abs_mul, e1, e2]

lemma qg_abs_cc_lt (m l : ℕ) (hm : 1 ≤ m) (hl : 1 ≤ l) (hlm : l ≤ m) :
    |centralCoeff m (l : ℤ)| < 1 / (l : ℝ) := by
  rw [qg_abs_cc m l hl hlm]
  have hpos : (0:ℝ) < ((m + l).choose l : ℝ) := by
    have : 0 < (m + l).choose l := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hlr : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  have h : ((m.choose l : ℕ) : ℝ) < (((m + l).choose l : ℕ) : ℝ) := by
    exact_mod_cast qg_choose_lt m l hm hl
  have h2 : ((m.choose l : ℝ) / ((m + l).choose l : ℝ)) < 1 := by
    rw [div_lt_one hpos]; exact h
  have : 0 < 1 / (l : ℝ) := by positivity
  nlinarith

lemma qg_cc_zero (m : ℕ) : centralCoeff m 0 = 0 := by simp [centralCoeff]

lemma qg_harm (m : ℕ) : ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ ≤ Real.log m + 1 := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  have h' : ((∑ i ∈ Finset.Icc 1 m, ((i : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1 + Real.log m := by exact_mod_cast h
  push_cast at h'
  simp only [one_div]
  linarith

lemma qg_sum_lt (m : ℕ) (hm : 1 ≤ m) :
    ∑ ℓ ∈ Finset.range (m + 1), |centralCoeff m (ℓ : ℤ)| < ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ := by
  have hI : Finset.Icc 1 m = Finset.Ico 1 (m+1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hI]
  simp only [Nat.cast_zero, qg_cc_zero, abs_zero, zero_add]
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨1, by simp only [Finset.mem_Ico]; omega⟩
  · intro l hl
    simp only [Finset.mem_Ico] at hl
    exact qg_abs_cc_lt m l hm hl.1 (by omega)

lemma qg_cc_neg (m : ℕ) (ℓ : ℤ) : centralCoeff m (-ℓ) = - centralCoeff m ℓ := by
  by_cases h : ℓ = 0
  · subst h; simp [centralCoeff]
  · have h' : -ℓ ≠ 0 := neg_ne_zero.mpr h
    simp only [centralCoeff, if_neg h, if_neg h', Int.natAbs_neg]
    have : (-1:ℝ)^(-ℓ-1) = (-1)^(ℓ-1) := by
      have e : (-ℓ-1) = (ℓ-1) + 2*(-ℓ) := by ring
      rw [e, zpow_add₀ (by norm_num), zpow_mul]
      norm_num
    rw [this]
    push_cast
    rw [div_neg]
    ring

lemma qg_abs_sum_le (m : ℕ) :
    ∑ ℓ ∈ Finset.Icc (-(m:ℤ)) m, |centralCoeff m ℓ| ≤
      2 * ∑ ℓ ∈ Finset.range (m + 1), |centralCoeff m (ℓ : ℤ)| := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(m:ℤ)) m) (fun ℓ => 0 ≤ ℓ)]
  have hA : ∑ ℓ ∈ (Finset.Icc (-(m:ℤ)) m).filter (fun ℓ => 0 ≤ ℓ), |centralCoeff m ℓ| =
      ∑ ℓ ∈ Finset.range (m + 1), |centralCoeff m (ℓ : ℤ)| := by
    apply Finset.sum_nbij' (fun ℓ : ℤ => ℓ.toNat) (fun i : ℕ => (i : ℤ))
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha; simp
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *
      rw [Int.toNat_of_nonneg ha.2]
  have hB : ∑ ℓ ∈ (Finset.Icc (-(m:ℤ)) m).filter (fun ℓ => ¬ 0 ≤ ℓ), |centralCoeff m ℓ| =
      ∑ ℓ ∈ Finset.Icc 1 m, |centralCoeff m (ℓ : ℤ)| := by
    apply Finset.sum_nbij' (fun ℓ : ℤ => (-ℓ).toNat) (fun i : ℕ => -(i : ℤ))
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha; simp
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at *
      rw [Int.toNat_of_nonneg (by omega), qg_cc_neg, abs_neg]
  have hC : ∑ ℓ ∈ Finset.Icc 1 m, |centralCoeff m (ℓ : ℤ)| ≤
      ∑ ℓ ∈ Finset.range (m + 1), |centralCoeff m (ℓ : ℤ)| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro i _ _; exact abs_nonneg _
  rw [hA, hB]
  linarith

theorem solution (m : ℕ) (hm : 1 ≤ m) (S : ℝ) (hS : 0 ≤ S) :
    (∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, (⌈|centralCoeff m ℓ| * S⌉₊ : ℝ)) ≤
        2 * m + S * ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ| ∧
      2 * m + S * ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ| ≤
        2 * m + S * (2 * Real.log m + 2) := by
  constructor
  · have h0 : (0:ℤ) ∈ Finset.Icc (-(m : ℤ)) m := by simp
    rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ (fun ℓ => |centralCoeff m ℓ|) h0]
    simp only [qg_cc_zero, abs_zero, zero_mul, Nat.ceil_zero, Nat.cast_zero, zero_add]
    have hcard : ((Finset.Icc (-(m : ℤ)) m).erase 0).card = 2 * m := by
      rw [Finset.card_erase_of_mem h0]; simp; omega
    calc ∑ ℓ ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (⌈|centralCoeff m ℓ| * S⌉₊ : ℝ)
        ≤ ∑ ℓ ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (|centralCoeff m ℓ| * S + 1) := by
          apply Finset.sum_le_sum
          intro ℓ _
          exact (Nat.ceil_lt_add_one (by positivity)).le
      _ = S * ∑ ℓ ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, |centralCoeff m ℓ| + 2 * m := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp only [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
          push_cast
          congr 1
          apply Finset.sum_congr rfl; intro ℓ _; ring
      _ = 2 * m + S * ∑ ℓ ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, |centralCoeff m ℓ| := by ring
  · have h1 := qg_abs_sum_le m
    have h2 := (qg_sum_lt m hm).le
    have h3 := qg_harm m
    have : ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ| ≤ 2 * Real.log m + 2 := by linarith
    nlinarith
