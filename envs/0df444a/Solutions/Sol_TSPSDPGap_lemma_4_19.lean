-- Prove2me | solution 1 for TSPSDPGap.lemma_4_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:48:43.148937+00:00
-- url     : https://prove2.me/submissions/32a7edbb-dc7a-487f-9c25-05366e74aae0

import Mathlib

namespace Aux_TSP419

theorem tele (θ : ℝ) (K : ℕ) :
    2 * Real.sin (θ / 2) * ∑ i ∈ Finset.Icc 1 K, Real.cos ((i : ℝ) * θ) =
      Real.sin (((K : ℝ) + 1 / 2) * θ) - Real.sin (θ / 2) := by
  induction K with
  | zero => simp; ring_nf
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih, Real.two_mul_sin_mul_cos]
    have e1 : θ / 2 - ((K + 1 : ℕ) : ℝ) * θ = -(((K : ℝ) + 1 / 2) * θ) := by push_cast; ring
    have e2 : θ / 2 + ((K + 1 : ℕ) : ℝ) * θ = (((K + 1 : ℕ) : ℝ) + 1 / 2) * θ := by
      push_cast; ring
    rw [e1, e2, Real.sin_neg]
    ring

theorem C_bound (d : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    (if Odd m then (-1 : ℝ) else 0) ≤
      ∑ i ∈ Finset.Icc 1 d, Real.cos (Real.pi * i * m / d) := by
  set θ : ℝ := Real.pi * m / d with hθ
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hc : ∀ i : ℕ, Real.cos (Real.pi * i * m / d) = Real.cos ((i : ℝ) * θ) := by
    intro i; congr 1; rw [hθ]; ring
  simp only [hc]
  by_cases hs : Real.sin (θ / 2) = 0
  · have hcos : Real.cos θ = 1 := by
      have h1 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
      rw [h1, Real.cos_two_mul, Real.cos_sq', hs]
      ring
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff θ).mp hcos
    have h1 : ∀ i ∈ Finset.Icc 1 d, Real.cos ((i : ℝ) * θ) = 1 := by
      intro i _
      rw [Real.cos_eq_one_iff]
      exact ⟨(i : ℤ) * n, by push_cast; rw [← hn]; ring⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (0 : ℝ) ≤ ((Finset.Icc 1 d).card : ℝ) := Nat.cast_nonneg _
    split_ifs <;> linarith
  · have ht := tele θ d
    have harg : ((d : ℝ) + 1 / 2) * θ = θ / 2 + (m : ℝ) * Real.pi := by
      rw [hθ]; field_simp <;> ring
    rw [harg, Real.sin_add_int_mul_pi] at ht
    have hsum : ∑ i ∈ Finset.Icc 1 d, Real.cos ((i : ℝ) * θ) = ((-1 : ℝ) ^ m - 1) / 2 := by
      apply mul_left_cancel₀ (show 2 * Real.sin (θ / 2) ≠ 0 by positivity)
      rw [ht]
      field_simp <;> ring
    rw [hsum]
    split_ifs with hm
    · rw [hm.neg_one_zpow]; norm_num
    · have : Even m := Int.not_odd_iff_even.mp hm
      rw [this.neg_one_zpow]; norm_num

end Aux_TSP419

open Aux_TSP419 in
theorem solution (d : ℕ) (j k : ℤ) :
    -(if Odd (j - k) then (1 : ℝ) else 0) ≤
      ∑ i ∈ Finset.Icc 1 d, Real.cos (Real.pi * i * j / d) * Real.cos (Real.pi * i * k / d) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty]
    split_ifs <;> norm_num
  have hsplit : ∀ i : ℕ, Real.cos (Real.pi * i * j / d) * Real.cos (Real.pi * i * k / d) =
      (Real.cos (Real.pi * i * ((j - k : ℤ) : ℝ) / d) +
        Real.cos (Real.pi * i * ((j + k : ℤ) : ℝ) / d)) / 2 := by
    intro i
    have e1 : Real.pi * i * ((j - k : ℤ) : ℝ) / d =
        Real.pi * i * j / d - Real.pi * i * k / d := by push_cast; ring
    have e2 : Real.pi * i * ((j + k : ℤ) : ℝ) / d =
        Real.pi * i * j / d + Real.pi * i * k / d := by push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  simp only [hsplit]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h1 := C_bound d hd (j - k)
  have h2 := C_bound d hd (j + k)
  have hpar : Odd (j + k) ↔ Odd (j - k) := by
    rw [Int.odd_iff, Int.odd_iff]; omega
  by_cases ho : Odd (j - k)
  · rw [if_pos ho] at h1 ⊢
    rw [if_pos (hpar.mpr ho)] at h2
    linarith
  · rw [if_neg ho] at h1 ⊢
    rw [if_neg (fun h => ho (hpar.mp h))] at h2
    linarith
