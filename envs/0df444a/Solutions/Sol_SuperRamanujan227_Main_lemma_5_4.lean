-- Prove2me | solution 1 for SuperRamanujan227.Main.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:11:10.25885+00:00
-- url     : https://prove2.me/submissions/3b61fac7-18eb-4d98-8d67-c3ca939ef406

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_FiniteFreeConvolution

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.L54
open SuperRamanujan227.Main

lemma coeff_q (L j i : ℕ) (hjL : j ≤ L) (hi : i ≤ L) :
    ((X ^ j * (X - 1) ^ (L - j) : ℝ[X])).coeff (L - i) = (-1) ^ i * ((L - j).choose i : ℝ) := by
  have h1 : (X - 1 : ℝ[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  rw [h1, coeff_X_pow_mul']
  by_cases hij : j ≤ L - i
  · rw [if_pos hij, coeff_X_add_C_pow]
    have : L - j - (L - i - j) = i := by omega
    have h2 : (L - j).choose (L - i - j) = (L - j).choose i := by
      rw [← Nat.choose_symm (by omega : i ≤ L - j)]; congr 1; omega
    rw [this, h2]
  · rw [if_neg hij]
    have : L - j < i := by omega
    simp [Nat.choose_eq_zero_of_lt this]

lemma cross (L j i : ℕ) (hjL : j ≤ L) (hi : i ≤ L) :
    (L - j).choose i * L.descFactorial j = (L - i).descFactorial j * L.choose i := by
  by_cases hij : i + j ≤ L
  · rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    have h1 := Nat.choose_mul (n := L) (k := i + j) (s := i) (by omega)
    have h2 := Nat.choose_mul (n := L) (k := i + j) (s := j) (by omega)
    have h3 : (i + j).choose i = (i + j).choose j := by
      rw [← Nat.choose_symm_add]
    simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] at h1 h2
    have e1 : L.choose (i + j) * (i + j).choose i = L.choose i * (L - i).choose j := h1
    have e2 : L.choose (i + j) * (i + j).choose j = L.choose j * (L - j).choose i := h2
    calc (L - j).choose i * (j.factorial * L.choose j) = j.factorial * (L.choose j * (L - j).choose i) := by ring
      _ = j.factorial * (L.choose i * (L - i).choose j) := by rw [← e2, ← e1, h3]
      _ = _ := by ring
  · have h1 : L - j < i := by omega
    have h2 : L - i < j := by omega
    rw [Nat.choose_eq_zero_of_lt h1, Nat.descFactorial_eq_zero_iff_lt.mpr h2]
    simp

lemma ratio (L j i : ℕ) (hjL : j ≤ L) (hi : i ≤ L) :
    ((L - j).choose i : ℝ) / (L.choose i : ℝ) = ((L - i).descFactorial j : ℝ) / (L.descFactorial j : ℝ) := by
  have hc : (L.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have hd : (L.descFactorial j : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hjL).ne'
  rw [div_eq_div_iff hc hd]
  exact_mod_cast cross L j i hjL hi

end SuperRamanujan227.Dev.L54

namespace SuperRamanujan227.Main
open SuperRamanujan227.Dev.L54

theorem chk_lemma_5_4 (L j : ℕ) (p : ℝ[X]) (hp : p.natDegree = L) (hj : 1 ≤ j) (hjL : j ≤ L) :
    ffMul L p (X ^ j * (X - 1) ^ (L - j)) =
      C (1 / (L.descFactorial j : ℝ)) * X ^ j * derivative^[j] p := by
  ext n
  have hLd : (L.descFactorial j : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hjL).ne'
  have hR : (C (1 / (L.descFactorial j : ℝ)) * X ^ j * derivative^[j] p).coeff n =
      if j ≤ n then (1 / (L.descFactorial j : ℝ)) * (((n - j + j).descFactorial j : ℕ) * p.coeff (n - j + j)) else 0 := by
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_iterate_derivative]
    by_cases hjn : j ≤ n
    · rw [if_pos hjn, if_pos hjn]; simp [nsmul_eq_mul]
    · rw [if_neg hjn, if_neg hjn]; simp
  rw [hR]
  unfold ffMul
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hn : n ≤ L
  · rw [Finset.sum_eq_single (L - n)]
    · have e : n = L - (L - n) := by omega
      rw [if_pos e]
      unfold ffCoeff
      rw [coeff_q L j (L - n) hjL (by omega)]
      have e2 : L - (L - n) = n := by omega
      rw [e2]
      have hc : (L.choose (L - n) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
      by_cases hjn : j ≤ n
      · rw [if_pos hjn]
        have := ratio L j (L - n) hjL (by omega)
        rw [e2] at this
        have e3 : n - j + j = n := by omega
        rw [e3]
        have : ((L - j).choose (L - n) : ℝ) / (L.choose (L - n) : ℝ) = (n.descFactorial j : ℝ) / (L.descFactorial j : ℝ) := this
        calc _ = p.coeff n * (((L - j).choose (L - n) : ℝ) / (L.choose (L - n) : ℝ)) := by
                have hu : ((-1:ℝ) ^ (L - n)) * ((-1:ℝ) ^ (L - n)) = 1 := by rw [← mul_pow]; simp
                generalize ((-1:ℝ) ^ (L - n)) = u at *
                generalize ((L - j).choose (L - n) : ℝ) = c
                have h4 : u * (u * p.coeff n) * (u * (u * c)) = p.coeff n * c := by
                  calc _ = (u * u) * (u * u) * (p.coeff n * c) := by ring
                    _ = _ := by rw [hu]; ring
                rw [h4, mul_div_assoc]
          _ = _ := by rw [this]; field_simp
      · rw [if_neg hjn]
        have : (L - j).choose (L - n) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [this]; simp
    · intro b hbm hb
      have := Finset.mem_range.mp hbm
      rw [if_neg]; omega
    · intro h; exfalso; apply h; simp
  · have hsum : (∑ x ∈ Finset.range (L + 1),
      if n = L - x then (-1) ^ x * ffCoeff L p x * ffCoeff L (X ^ j * (X - 1) ^ (L - j)) x / (L.choose x : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg]
      have := Finset.mem_range.mp hb
      omega
    rw [hsum]
    have hz : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    by_cases hjn : j ≤ n
    · rw [if_pos hjn, show n - j + j = n by omega, hz]; simp only [mul_zero]
    · rw [if_neg hjn]

end SuperRamanujan227.Main
end

theorem solution : type_of% @SuperRamanujan227.Main.chk_lemma_5_4 := @SuperRamanujan227.Main.chk_lemma_5_4
