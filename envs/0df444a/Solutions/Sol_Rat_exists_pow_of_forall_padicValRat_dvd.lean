-- Prove2me | solution 1 for Rat.exists_pow_of_forall_padicValRat_dvd
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:00:43.609014+00:00
-- url     : https://prove2.me/submissions/2c7b3025-0812-4402-98d0-bdc74ef7eb87

import Mathlib

set_option autoImplicit false

noncomputable section

private theorem nat_exists_pow_of_factorization_dvd (m : ℕ) (hm : m ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → 71 ∣ m.factorization p) :
    ∃ b : ℕ, b ^ 71 = m := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 71), ?_⟩
  rw [← Finset.prod_pow]
  calc
    (∏ p ∈ m.primeFactors, (p ^ (m.factorization p / 71)) ^ 71) =
        ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, Nat.div_mul_cancel (h p (Nat.prime_of_mem_primeFactors hp))]
    _ = m := Nat.prod_factorization_pow_eq_self hm

namespace Rat

/-- A nonzero rational number whose every prime valuation is divisible by 71
is a 71st power in the rationals. -/
theorem _root_.solution (a : ℚ) (ha : a ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → (71 : ℤ) ∣ padicValRat p a) :
    ∃ b : ℚ, b ^ 71 = a := by
  have hcop (p : ℕ) (hp : Nat.Prime p) : ¬ (p ∣ a.num.natAbs ∧ p ∣ a.den) := by
    intro hboth
    have hg := Nat.dvd_gcd hboth.1 hboth.2
    rw [a.reduced] at hg
    exact hp.not_dvd_one hg
  have hnum : ∀ p : ℕ, Nat.Prime p → 71 ∣ a.num.natAbs.factorization p := by
    intro p hp
    by_cases hn : p ∣ a.num.natAbs
    · have hd : ¬ p ∣ a.den := fun hd => hcop p hp ⟨hn, hd⟩
      have hv := h p hp
      rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero,
        sub_zero, ← Nat.factorization_def _ hp] at hv
      exact_mod_cast hv
    · simp [Nat.factorization_eq_zero_of_not_dvd hn]
  have hden : ∀ p : ℕ, Nat.Prime p → 71 ∣ a.den.factorization p := by
    intro p hp
    by_cases hd : p ∣ a.den
    · have hn : ¬ p ∣ a.num.natAbs := fun hn => hcop p hp ⟨hn, hd⟩
      have hv := h p hp
      rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hn, Nat.cast_zero,
        zero_sub, ← Nat.factorization_def _ hp, Int.dvd_neg] at hv
      exact_mod_cast hv
    · simp [Nat.factorization_eq_zero_of_not_dvd hd]
  obtain ⟨N, hN⟩ := nat_exists_pow_of_factorization_dvd a.num.natAbs
    (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr ha)) hnum
  obtain ⟨D, hD⟩ := nat_exists_pow_of_factorization_dvd a.den a.den_nz hden
  have hNq : (N : ℚ) ^ 71 = (a.num.natAbs : ℚ) := by exact_mod_cast hN
  have hDq : (D : ℚ) ^ 71 = (a.den : ℚ) := by exact_mod_cast hD
  by_cases hsign : 0 ≤ a.num
  · refine ⟨(N : ℚ) / D, ?_⟩
    rw [div_pow, hNq, hDq]
    have he : (a.num.natAbs : ℚ) = (a.num : ℚ) := by
      have heZ : (a.num.natAbs : ℤ) = a.num := Int.natAbs_of_nonneg hsign
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) heZ
    rw [he]
    exact a.num_div_den
  · refine ⟨-((N : ℚ) / D), ?_⟩
    rw [neg_pow, div_pow, hNq, hDq]
    have he : (a.num.natAbs : ℚ) = -(a.num : ℚ) := by
      have heZ : (a.num.natAbs : ℤ) = -a.num :=
        Int.ofNat_natAbs_of_nonpos (le_of_not_ge hsign)
      simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : ℚ)) heZ
    rw [he]
    norm_num
    simpa only [neg_div, neg_neg] using a.num_div_den

end Rat
