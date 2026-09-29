-- Prove2me | solution 1 for Polynomial.exists_eval_eq_coeff_zero_add_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d18ac911-c981-52f1-bdac-9f337e5e098c

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul

private theorem natCast_dvd_pow_self_of_forall_prime_dvd {N : ℤ} (hN : N ≠ 0) {d : ℕ}
    (hd : d ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ d → (q : ℤ) ∣ N) : (d : ℤ) ∣ N ^ d := by
  have hn : N.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hN
  rw [Int.natCast_dvd, Int.natAbs_pow,
    ← Nat.factorization_prime_le_iff_dvd hd (pow_ne_zero d hn)]
  intro q hq
  rcases eq_or_ne (d.factorization q) 0 with h0 | h0
  · simp [h0]
  · have hqn : q ∣ N.natAbs := Int.natCast_dvd.1 (h q hq (Nat.dvd_of_factorization_pos h0))
    exact (Nat.factorization_lt q hd).le.trans
      ((hq.pow_dvd_iff_le_factorization (pow_ne_zero d hn)).1 (pow_dvd_pow_of_dvd hqn d))

theorem solution (p : Polynomial ℚ) (N : ℤ) (hN : N ≠ 0) (hden : ∀ k : ℕ, ∀ q : ℕ, q.Prime → q ∣ (p.coeff k).den → (q : ℤ) ∣ N) : ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ m : ℤ, ∃ z : ℤ, p.eval ((N : ℚ) ^ K * m) = p.coeff 0 + (N : ℚ) ^ (K - K₀) * z := by

  suffices h : ∃ K₀ : ℕ, ∀ k : ℕ, ∃ c : ℤ, (c : ℚ) = p.coeff k * (N : ℚ) ^ K₀ by
    obtain ⟨K₀, key⟩ := h
    choose c hc using key
    refine ⟨K₀, fun K hK m => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
    refine ⟨∑ i ∈ Finset.range p.natDegree, c (i + 1) * N ^ ((K₀ + j) * i) * m ^ (i + 1), ?_⟩
    rw [Nat.add_sub_cancel_left, Polynomial.eval_eq_sum_range, Finset.sum_range_succ', pow_zero,
      mul_one]
    push_cast
    rw [add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    ring

  refine ⟨∑ k ∈ p.support, (p.coeff k).den, fun k => ?_⟩
  by_cases hk : k ∈ p.support
  · have hle : (p.coeff k).den ≤ ∑ k ∈ p.support, (p.coeff k).den :=
      Finset.single_le_sum (f := fun k => (p.coeff k).den) (fun i _ => Nat.zero_le _) hk
    obtain ⟨t, ht⟩ : ((p.coeff k).den : ℤ) ∣ N ^ ∑ k ∈ p.support, (p.coeff k).den :=
      (natCast_dvd_pow_self_of_forall_prime_dvd hN (p.coeff k).den_nz (hden k)).trans
        (pow_dvd_pow N hle)
    refine ⟨(p.coeff k).num * t, ?_⟩
    have ht' : (N : ℚ) ^ (∑ k ∈ p.support, (p.coeff k).den) = ((p.coeff k).den : ℚ) * (t : ℚ) :=
      mod_cast ht
    rw [ht', ← mul_assoc, Rat.mul_den_eq_num, Int.cast_mul]
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hk]⟩

end S_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul
end P2MW
export P2MW.S_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul (solution)
