-- Prove2me | solution 1 for TaoFivePrimes.three_primes_of_representationCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T02:20:31.779712+00:00
-- url     : https://prove2.me/submissions/a6452a7c-122e-4220-b1f6-b79a40d4b76e

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Lean.Elab.Tactic.Omega

/-!
# Extracting the three odd primes from Tao's weighted count

This proves the implication following equation (8.10) in
https://arxiv.org/abs/1201.6656. Positivity of the count is an explicit hypothesis;
no analytic lower bound is assumed to have been proved.
-/

namespace TaoRepresentationProof

open TaoFivePrimes

/-- A nonzero sifted term in its permitted range represents an odd prime. -/
theorem prime_and_odd_of_sifted_ne_zero {n N : ℕ} (hN : 4 ≤ N) (hnN : n ≤ N)
    (h : siftedVonMangoldt N n ≠ 0) : n.Prime ∧ Odd n := by
  have hc : n.Coprime (primorial (Nat.sqrt N)) := by
    by_contra hn
    simp [siftedVonMangoldt, hn] at h
  have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    simpa only [siftedVonMangoldt, if_pos hc] using h
  have hn : 2 ≤ n := by
    by_contra hsmall
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp at hΛ
  have hp : n.Prime := by
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨hn, ?_⟩
    intro m hm hmsqrt hmn
    have hprime : (Nat.minFac m).Prime := Nat.minFac_prime (by omega)
    have hpn : Nat.minFac m ∣ n := (Nat.minFac_dvd m).trans hmn
    have hbound : Nat.minFac m ≤ Nat.sqrt N :=
      (Nat.minFac_le (by omega)).trans (hmsqrt.trans (Nat.sqrt_le_sqrt hnN))
    have hpp : Nat.minFac m ∣ primorial (Nat.sqrt N) :=
      hprime.dvd_primorial_iff.mpr hbound
    exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hc hpn hpp)
  refine ⟨hp, hp.odd_of_ne_two ?_⟩
  intro hn2
  have h2sqrt : 2 ≤ Nat.sqrt N := Nat.le_sqrt.mpr hN
  have h2prim : 2 ∣ primorial (Nat.sqrt N) :=
    Nat.prime_two.dvd_primorial_iff.mpr h2sqrt
  have h2n : 2 ∣ n := by rw [hn2]
  exact Nat.prime_two.ne_one (Nat.eq_one_of_dvd_coprimes hc h2n h2prim)

end TaoRepresentationProof

open TaoFivePrimes TaoRepresentationProof

/-- A positive count in equation (8.10) supplies the witnesses required by Theorem 8.2. -/
theorem solution (x H : ℕ)
    (hx : 4000 ≤ x) (hcount : 0 < representationCount x H) :
    ∃ m : ℕ, x ≤ m + H ∧ m + 2 ≤ x ∧
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
        Odd p₁ ∧ Odd p₂ ∧ Odd p₃ ∧ p₁ + p₂ + p₃ = m := by
  have hnonzero := ne_of_gt hcount
  unfold representationCount at hnonzero
  obtain ⟨n₁, hn₁, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  obtain ⟨n₂, hn₂, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  obtain ⟨n₃, hn₃, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  obtain ⟨h₁, hh₁, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  obtain ⟨h₂, hh₂, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  obtain ⟨h₃, hh₃, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  have heq : x = n₁ + n₂ + n₃ + h₁ + h₂ + h₃ := by
    by_contra h
    simp only [if_neg h, ne_eq, not_true_eq_false] at hnonzero
  rw [if_pos heq] at hnonzero
  have hs₁ : siftedVonMangoldt x n₁ ≠ 0 := by
    intro h
    simp only [h, zero_mul, ne_eq, not_true_eq_false] at hnonzero
  have hs₂ : siftedVonMangoldt x n₂ ≠ 0 := by
    intro h
    simp only [h, mul_zero, zero_mul, ne_eq, not_true_eq_false] at hnonzero
  have hs₃ : siftedVonMangoldt (x / 1000) n₃ ≠ 0 := by
    intro h
    simp only [h, mul_zero, zero_mul, ne_eq, not_true_eq_false] at hnonzero
  have hp₁ := prime_and_odd_of_sifted_ne_zero (by omega : 4 ≤ x)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hn₁)) hs₁
  have hp₂ := prime_and_odd_of_sifted_ne_zero (by omega : 4 ≤ x)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hn₂)) hs₂
  have hp₃ := prime_and_odd_of_sifted_ne_zero (by omega : 4 ≤ x / 1000)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hn₃)) hs₃
  obtain ⟨hh₁lo, hh₁hi⟩ := Finset.mem_Icc.mp hh₁
  obtain ⟨hh₂lo, hh₂hi⟩ := Finset.mem_Icc.mp hh₂
  obtain ⟨hh₃lo, hh₃hi⟩ := Finset.mem_Icc.mp hh₃
  refine ⟨n₁ + n₂ + n₃, ?_, ?_, n₁, n₂, n₃, hp₁.1, hp₂.1, hp₃.1,
    hp₁.2, hp₂.2, hp₃.2, rfl⟩ <;> omega
