-- Prove2me | solution 1 for OPG37364.card_divisors_pow_five_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T06:19:21.212792+00:00
-- url     : https://prove2.me/submissions/5997a0a7-d127-490e-ad00-6395c89a4379

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace OPG37364.DivisorBound

theorem exponent_large_base (e : ℕ) : (e + 1)^5 ≤ 32^e := by
  calc
    (e + 1)^5 ≤ (2^e)^5 := Nat.pow_le_pow_left (Nat.succ_le_of_lt Nat.lt_two_pow_self) 5
    _ = 32^e := by rw [← pow_mul, Nat.mul_comm e 5, pow_mul]; norm_num

theorem exponent_small_base (e : ℕ) : (e + 1)^5 ≤ 512 * 2^e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e ≤ 6
    · interval_cases e <;> norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 7 ≤ e by omega)
      have hprev := ih (6+k) (by omega)
      have hstep : (k+8)^5 ≤ 2*(k+7)^5 := by ring_nf; omega
      calc
        (7+k+1)^5 ≤ 2*(6+k+1)^5 := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep
        _ ≤ 2*(512*2^(6+k)) := Nat.mul_le_mul_left 2 hprev
        _ = 512*2^(7+k) := by rw [show 7+k=(6+k)+1 by omega, pow_succ]; ring

theorem prime_exponent (p e : ℕ) (hp : p.Prime) :
    (e+1)^5 ≤ (if p < 32 then 512 else 1) * p^e := by
  split_ifs with h
  · exact (exponent_small_base e).trans (Nat.mul_le_mul_left 512
      (Nat.pow_le_pow_left hp.two_le e))
  · simpa using (exponent_large_base e).trans (Nat.pow_le_pow_left (by omega : 32 ≤ p) e)

end OPG37364.DivisorBound

namespace OPG37364

/-- An explicit fifth-power bound for the number of positive divisors. -/
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    n.divisors.card ^ 5 ≤ 512^32 * n := by
  classical
  have hc : (n.primeFactors.filter (· < 32)).card ≤ 32 := by
    simpa using Finset.card_le_card (show n.primeFactors.filter (· < 32) ⊆
      Finset.range 32 from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
  have hprod : (∏ p ∈ n.primeFactors, (if p < 32 then 512 else 1 : ℕ)) =
      512 ^ (n.primeFactors.filter (· < 32)).card := by
    rw [← Finset.prod_filter]; simp
  rw [Nat.card_divisors hn.ne', ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p+1)^5) ≤
        ∏ p ∈ n.primeFactors, (if p < 32 then 512 else 1) * p^(n.factorization p) :=
      Finset.prod_le_prod' fun p hp => DivisorBound.prime_exponent p _
        (Nat.prime_of_mem_primeFactors hp)
    _ = 512 ^ (n.primeFactors.filter (· < 32)).card * n := by
      rw [Finset.prod_mul_distrib, hprod, ← Nat.prod_primeFactors_pow_factorization hn.ne']
    _ ≤ 512^32 * n := Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by decide) hc)

end OPG37364
