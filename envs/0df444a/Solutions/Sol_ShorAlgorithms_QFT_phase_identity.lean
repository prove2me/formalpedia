-- Prove2me | solution 1 for ShorAlgorithms.QFT.phase_identity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:53:35.087709+00:00
-- url     : https://prove2.me/submissions/4628e8ff-ca6b-4daf-a1bc-6ac124b39558

import Mathlib
import Definitions.Def_ShorAlgorithms_QFT_BitStrings
open ShorAlgorithms.QFT
namespace AQFT

lemma ratio_le {l : ℕ} (j k : Fin l) (hjk : j ≤ k) :
    (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l = 1 / (2 * 2 ^ ((k : ℕ) - j)) := by
  have hn : (j : ℕ) + (k.rev : ℕ) + ((k : ℕ) - j) + 1 = l := by
    simp only [Fin.val_rev]
    omega
  have he : (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) * 2 ^ ((k : ℕ) - j) * 2 = 2 ^ l := by
    rw [← pow_add, ← pow_add, ← pow_succ, hn]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  nlinarith

lemma ratio_gt {l : ℕ} (j k : Fin l) (hjk : k < j) :
    (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l = 2 ^ ((j : ℕ) - k - 1) := by
  have hn : (j : ℕ) + (k.rev : ℕ) = ((j : ℕ) - k - 1) + l := by
    simp only [Fin.val_rev]
    omega
  rw [← pow_add, hn, pow_add]
  field_simp

lemma pair_phase {l : ℕ} (a b : Fin l → Fin 2) (j k : Fin l) :
    Complex.exp (((if j ≤ k then
      Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0 : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) /
      2 ^ l * (a j : ℕ) * (b k : ℕ) : ℝ) : ℂ) * Complex.I) := by
  by_cases hjk : j ≤ k
  · rw [if_pos hjk]
    congr 3
    have hr := ratio_le j k hjk
    calc Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
        = (2 * Real.pi) * (1 / (2 * 2 ^ ((k : ℕ) - j))) * (a j : ℕ) * (b k : ℕ) := by ring
      _ = _ := by rw [← hr]; ring
  · rw [if_neg hjk]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    have hr := ratio_gt j k (lt_of_not_ge hjk)
    have he : 2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) /
      2 ^ l * (a j : ℕ) * (b k : ℕ) =
      (2 ^ ((j : ℕ) - k - 1) * (a j : ℕ) * (b k : ℕ) : ℕ) * (2 * Real.pi) := by
      push_cast
      rw [show 2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l =
        (2 * Real.pi) * ((2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l) by ring, hr]
      ring
    rw [he]
    push_cast
    rw [mul_assoc]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Complex.exp_nat_mul_two_pi_mul_I (2 ^ ((j : ℕ) - k - 1) * (a j : ℕ) * (b k : ℕ))).symm

lemma sum_phase {l : ℕ} (a b : Fin l → Fin 2) :
    (∑ j : Fin l, ∑ k : Fin l, if j ≤ k then
      Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0) =
    (∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
      ∑ j : Fin l, ∑ k : Fin l, if j < k then
        Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0 := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he (k : Fin l) : (if j ≤ k then Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0) =
      (if k = j then Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ) else 0) +
      (if j < k then Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0) := by
    rcases lt_trichotomy j k with h | rfl | h
    · simp [h.le, h, h.ne']
    · simp
    · simp [not_le_of_gt h, not_lt_of_gt h, h.ne]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma reversed_value {l : ℕ} (b : Fin l → Fin 2) :
    (bitsVal (bitRev b) : ℝ) = ∑ k : Fin l, (2 : ℝ) ^ (k.rev : ℕ) * (b k : ℕ) := by
  simp only [bitsVal, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, bitRev]
  simpa [Fin.revPerm] using (Equiv.sum_comp Fin.revPerm (fun k : Fin l => (2 : ℝ) ^ (k.rev : ℕ) * (b k : ℕ)))

lemma phase_identity (l : ℕ) (a b : Fin l → Fin 2) :
    Complex.exp
        (((∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
            ∑ j : Fin l, ∑ k : Fin l,
              if j < k then
                Real.pi / 2 ^ ((k : ℕ) - (j : ℕ)) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
              else 0 : ℝ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (bitsVal a : ℂ) * (bitsVal (bitRev b) : ℂ) /
        2 ^ l) := by
  classical
  have he : (∑ j : Fin l, ∑ k : Fin l,
      2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l * (a j : ℕ) * (b k : ℕ)) =
      2 * Real.pi * (bitsVal a : ℝ) * (bitsVal (bitRev b) : ℝ) / 2 ^ l := by
    rw [reversed_value]
    simp only [bitsVal, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← sum_phase]
  calc
    _ = Complex.exp (((∑ j : Fin l, ∑ k : Fin l,
        2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l * (a j : ℕ) * (b k : ℕ)) : ℝ) * Complex.I) := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      simp_rw [pair_phase]
    _ = _ := by
      rw [he]
      congr 1
      push_cast
      ring

end AQFT

theorem solution (l : ℕ) (a b : Fin l → Fin 2) :
    Complex.exp
        (((∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
            ∑ j : Fin l, ∑ k : Fin l,
              if j < k then
                Real.pi / 2 ^ ((k : ℕ) - (j : ℕ)) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
              else 0 : ℝ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (bitsVal a : ℂ) * (bitsVal (bitRev b) : ℂ) /
        2 ^ l)  := AQFT.phase_identity l a b
