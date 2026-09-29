-- Prove2me | solution 1 for OddPerfectNumber.dris_packaged_cofactor_odd
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T19:20:13.052287+00:00
-- url     : https://prove2.me/submissions/25fa662d-3da8-456b-a92f-48772f88cc03

import Mathlib

open Finset

namespace DrisParityAux

/-- `σ(p^k)` as a geometric sum. -/
lemma sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ range (k + 1), p ^ i := by
  rw [Nat.sum_divisors_prime_pow hp]

/-- Peeling off the constant term of a geometric sum. -/
lemma geom_succ (q n : ℕ) : ∑ i ∈ range (n + 1), q ^ i = q * (∑ i ∈ range n, q ^ i) + 1 := by
  rw [Finset.sum_range_succ']
  simp [Finset.mul_sum, pow_succ, mul_comm]

/-- Geometric sums mod `r`, when `p ≡ 1 [MOD r]`. -/
lemma geom_mod (p n r : ℕ) (h : p % r = 1 % r) :
    (∑ i ∈ range n, p ^ i) % r = n % r := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ range n, p ^ i % r = 1 % r := by
    intro i _
    rw [Nat.pow_mod, h, ← Nat.pow_mod, one_pow]
  rw [Finset.sum_congr rfl this]
  simp [Finset.sum_const]

/-- The divisor sum of a square, factored into its local divisor sums. -/
lemma sigma_sq_local_prod {m : ℕ} (hm : m ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x) =
      ∏ q ∈ (m ^ 2).primeFactors, ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
  have hm2 : (m ^ 2) ≠ 0 := pow_ne_zero _ hm
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization
    (ArithmeticFunction.sigma 1) hm2
  rw [ArithmeticFunction.sigma_one_apply] at h
  rw [h, Finsupp.prod]
  rw [Nat.support_factorization]
  refine Finset.prod_congr rfl ?_
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  rw [ArithmeticFunction.sigma_one_apply, sigma_prime_pow q _ hqp]

/-- The divisor sum of a nonzero square is odd — with no parity assumption on the base. -/
lemma sigma_sq_odd {m : ℕ} (hm0 : m ≠ 0) : (∑ x ∈ (m ^ 2).divisors, x) % 2 = 1 := by
  rw [sigma_sq_local_prod hm0, Finset.prod_nat_mod]
  have hloc : ∀ q ∈ (m ^ 2).primeFactors,
      (∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i) % 2 = 1 := by
    intro q hq
    have hE : (m ^ 2).factorization q = 2 * m.factorization q := by
      rw [Nat.factorization_pow]; simp
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    rcases hqp.eq_two_or_odd with h2 | hodd
    · subst h2
      rw [geom_succ]
      omega
    · rw [geom_mod q ((m ^ 2).factorization q + 1) 2 (by omega), hE]
      omega
  rw [Finset.prod_congr rfl hloc]
  simp

end DrisParityAux

/-- **The parity bridge.**  In the packaged Euler configuration `σ(p^k) = 2t`, `m² = t·d`,
`σ(m²) = p^k·d` with `p ≡ k ≡ 1 (mod 4)`, the cofactor `m` is odd. -/
theorem solution (p k m t d : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (p ^ k).divisors, x) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d) :
    Odd m := by
  -- `σ(p^k) ≡ k + 1 ≡ 2 (mod 4)`, so `t` is odd
  have hgeom : (∑ x ∈ (p ^ k).divisors, x) = ∑ i ∈ range (k + 1), p ^ i :=
    DrisParityAux.sigma_prime_pow p k hp
  have hmod : (∑ i ∈ range (k + 1), p ^ i) % 4 = (k + 1) % 4 :=
    DrisParityAux.geom_mod p (k + 1) 4 (by omega)
  have htodd : t % 2 = 1 := by
    rw [← hgeom, hsig] at hmod
    omega
  -- the last two identities multiply to `σ(m²) · t = p^k · m²`
  have hkey : (∑ x ∈ (m ^ 2).divisors, x) * t = p ^ k * m ^ 2 := by
    rw [hsigm, hdvd]; ring
  -- the left-hand side is odd, hence so is the right-hand side
  have hsigodd : (∑ x ∈ (m ^ 2).divisors, x) % 2 = 1 := DrisParityAux.sigma_sq_odd hm0
  have hlhs : ((∑ x ∈ (m ^ 2).divisors, x) * t) % 2 = 1 := by
    rw [Nat.mul_mod, hsigodd, htodd]
  rw [hkey] at hlhs
  rcases Nat.even_or_odd m with hev | hodd
  · exfalso
    have h2m : (2 : ℕ) ∣ m := hev.two_dvd
    have : (2 : ℕ) ∣ p ^ k * m ^ 2 :=
      Dvd.dvd.mul_left (h2m.trans (dvd_pow_self m two_ne_zero)) _
    omega
  · exact hodd
