-- Prove2me | solution 1 for TSPSDPGap.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:32:24.566921+00:00
-- url     : https://prove2.me/submissions/0f1ed917-7844-4270-ad3a-dab93311461e

import Mathlib
import Definitions.Def_TSPSDPGap_coeffB

namespace Aux_TSPSDPGap_lemma_4_11

theorem sum_id (h : ℕ) : ∑ j ∈ Finset.Ico 1 (h + 1), (j : ℝ) = (h : ℝ) * ((h : ℝ) + 1) / 2 := by
  induction h with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1), ih]
    push_cast
    ring

theorem gauss (h : ℕ) :
    ∑ j ∈ Finset.Ico 1 (h + 1), (((h + 1 : ℕ) : ℝ) - j) = ((h + 1 : ℕ) : ℝ) * ((h : ℝ)) / 2 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, sum_id,
    Nat.add_sub_cancel]
  push_cast
  ring

theorem tel (x : ℝ) (M : ℕ) :
    2 * Real.sin (x / 2) * ∑ i ∈ Finset.Icc 1 M, Real.cos ((i : ℝ) * x)
      = Real.sin (((M : ℝ) + 1 / 2) * x) - Real.sin (x / 2) := by
  induction M with
  | zero =>
    have e : (((0 : ℕ) : ℝ) + 1 / 2) * x = x / 2 := by push_cast; ring
    rw [e, Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    have e1 : (((k + 1 : ℕ) : ℝ) + 1 / 2) * x = ((k + 1 : ℕ) : ℝ) * x + x / 2 := by ring
    have e2 : ((k : ℝ) + 1 / 2) * x = ((k + 1 : ℕ) : ℝ) * x - x / 2 := by push_cast; ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring

theorem cos_sum (m j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < 2 * (m + 1)) :
    ∑ i ∈ Finset.Icc 1 m, Real.cos (Real.pi * (i : ℝ) * (j : ℝ) / ((m + 1 : ℕ) : ℝ))
      = -(1 + (-1 : ℝ) ^ j) / 2 := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.pi * j / ((m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hd : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hsum : ∑ i ∈ Finset.Icc 1 m, Real.cos (Real.pi * (i : ℝ) * (j : ℝ) / ((m + 1 : ℕ) : ℝ))
      = ∑ i ∈ Finset.Icc 1 m, Real.cos ((i : ℝ) * x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hx]
    congr 1
    ring
  have hsin : Real.sin (((m : ℝ) + 1 / 2) * x) = -((-1 : ℝ) ^ j) * Real.sin (x / 2) := by
    have e : ((m : ℝ) + 1 / 2) * x = (j : ℝ) * Real.pi - x / 2 := by
      rw [hx]
      push_cast
      field_simp <;> ring
    rw [e, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    ring
  have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
  have hs : Real.sin (x / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hx]
      exact div_pos (div_pos (mul_pos Real.pi_pos hjpos) hd) two_pos
    · rw [hx, div_div, div_lt_iff₀ (by positivity)]
      have : (j : ℝ) < ((m + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast (by omega : j < (m + 1) * 2)
      nlinarith [Real.pi_pos]
  have ht := tel x m
  rw [hsin] at ht
  rw [hsum]
  apply mul_left_cancel₀ hs
  linear_combination (1 / 2 : ℝ) * ht

end Aux_TSPSDPGap_lemma_4_11

open TSPSDPGap Aux_TSPSDPGap_lemma_4_11 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    ∑ i ∈ Finset.Icc 1 (n / 2), coeffB g n i = 1 := by
  obtain ⟨d, hdd⟩ : ∃ d, n / 2 = d := ⟨_, rfl⟩
  have hn2 : 2 ∣ n := (even_iff_two_dvd.mp hg).trans hgn
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hn : n = 2 * (m + 1) := by omega
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have hnR : (n : ℝ) = 2 * ((m : ℝ) + 1) := by rw [hn]; push_cast; ring
  have hgn' : (g : ℝ) < n := by exact_mod_cast hlt
  have hng : (n : ℝ) - g ≠ 0 := by linarith
  have hg0 : (g : ℝ) ≠ 0 := by linarith
  have hg1 : (g : ℝ) - 1 ≠ 0 := by linarith
  have hm0 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd' : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hcancel : ∀ X : ℝ, ((n : ℝ) - g) * (1 / ((n : ℝ) - g) * X) = X := by
    intro X
    rw [← mul_assoc, mul_one_div_cancel hng, one_mul]
  have hB1 : ∀ i ∈ Finset.Icc 1 m, coeffB g n i =
      (2 * (g : ℝ) - (2 + 4 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g,
        ((g : ℝ) - j) * Real.cos (Real.pi * i * j / ((m + 1 : ℕ) : ℝ)))) /
        ((n : ℝ) * ((g : ℝ) - 1)) := by
    intro i hi
    have hi' : i < n / 2 := by rw [Finset.mem_Icc] at hi; omega
    unfold coeffB coeffA
    rw [if_pos hi', if_pos hi', hdd, hcancel]
  have hB2 : coeffB g n (m + 1) =
      ((g : ℝ) - (1 + 2 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g,
        ((g : ℝ) - j) * Real.cos (Real.pi * ((m + 1 : ℕ) : ℝ) * j / ((m + 1 : ℕ) : ℝ)))) /
        ((n : ℝ) * ((g : ℝ) - 1)) := by
    have hi' : ¬ (m + 1 < n / 2) := by omega
    unfold coeffB coeffA
    rw [if_neg hi', if_neg hi', hdd, hcancel]
  have hC : ∀ j ∈ Finset.Ico 1 g, ∑ i ∈ Finset.Icc 1 m,
      Real.cos (Real.pi * (i : ℝ) * (j : ℝ) / ((m + 1 : ℕ) : ℝ)) = -(1 + (-1 : ℝ) ^ j) / 2 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact cos_sum m j (by omega) (by omega)
  have hS : ∑ i ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Ico 1 g,
      ((g : ℝ) - j) * Real.cos (Real.pi * i * j / ((m + 1 : ℕ) : ℝ))
      = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-(1 + (-1 : ℝ) ^ j) / 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← Finset.mul_sum, hC j hj]
  have hT : ∑ j ∈ Finset.Ico 1 g,
      ((g : ℝ) - j) * Real.cos (Real.pi * ((m + 1 : ℕ) : ℝ) * j / ((m + 1 : ℕ) : ℝ))
      = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-1 : ℝ) ^ j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have e : Real.pi * ((m + 1 : ℕ) : ℝ) * j / ((m + 1 : ℕ) : ℝ) = (j : ℝ) * Real.pi := by
      rw [mul_right_comm, mul_div_cancel_right₀ _ hd']
      ring
    rw [e, Real.cos_nat_mul_pi]
  obtain ⟨h, rfl⟩ : ∃ h, g = h + 1 := ⟨g - 1, by omega⟩
  have hG := gauss h
  obtain ⟨T, hTdef⟩ : ∃ T, T = ∑ j ∈ Finset.Ico 1 (h + 1), (((h + 1 : ℕ) : ℝ) - j) * (-1 : ℝ) ^ j :=
    ⟨_, rfl⟩
  have hS2 : ∑ j ∈ Finset.Ico 1 (h + 1), (((h + 1 : ℕ) : ℝ) - j) * (-(1 + (-1 : ℝ) ^ j) / 2)
      = -(((h + 1 : ℕ) : ℝ) * (h : ℝ) / 2 + T) / 2 := by
    rw [hTdef, ← hG]
    calc ∑ j ∈ Finset.Ico 1 (h + 1), (((h + 1 : ℕ) : ℝ) - j) * (-(1 + (-1 : ℝ) ^ j) / 2)
        = ∑ j ∈ Finset.Ico 1 (h + 1), ((-(1 / 2 : ℝ)) * (((h + 1 : ℕ) : ℝ) - j)
            + (-(1 / 2 : ℝ)) * ((((h + 1 : ℕ) : ℝ) - j) * (-1 : ℝ) ^ j)) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  rw [hdd, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), Finset.sum_congr rfl hB1, hB2, hT,
    ← hTdef]
  have hlin : ∀ i ∈ Finset.Icc 1 m,
      (2 * ((h + 1 : ℕ) : ℝ) - (2 + 4 / ((h + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.Ico 1 (h + 1),
        (((h + 1 : ℕ) : ℝ) - j) * Real.cos (Real.pi * i * j / ((m + 1 : ℕ) : ℝ)))) /
        ((n : ℝ) * (((h + 1 : ℕ) : ℝ) - 1))
      = (2 * ((h + 1 : ℕ) : ℝ) - 2) / ((n : ℝ) * (((h + 1 : ℕ) : ℝ) - 1)) +
        (-(4 / ((h + 1 : ℕ) : ℝ)) / ((n : ℝ) * (((h + 1 : ℕ) : ℝ) - 1))) *
        ∑ j ∈ Finset.Ico 1 (h + 1),
          (((h + 1 : ℕ) : ℝ) - j) * Real.cos (Real.pi * i * j / ((m + 1 : ℕ) : ℝ)) := by
    intro i _
    ring
  rw [Finset.sum_congr rfl hlin, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, hS,
    hS2, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, hnR]
  have a1 : (h : ℝ) + 1 ≠ 0 := by positivity
  have a2 : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  try simp only [add_sub_cancel_right]
  field_simp <;> ring
