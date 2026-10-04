-- Prove2me | solution 1 for OddPerfectNumber.euler_form
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T21:37:12.29885+00:00
-- url     : https://prove2.me/submissions/7fa3fc9e-8ea4-4aae-bc54-519b389a3fad

/-
Compatibility port of an existing formalization; not an original proof.
Upstream author: umpolungfish.
Upstream repository: https://github.com/umpolungfish/odd-perfect-numbers
Upstream commit: 11d77f496a96085c16d6e4f213c73a0c20dc651e
Upstream file: OddPerfectNumbers.lean
License: released to the public domain under the Unlicense, as explicitly
stated in README.md at the same commit. The original author and references
are retained below. The separate upstream Challenge.lean stub is not used.

This compatibility port targets Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
The upstream proof body is initially unchanged. Exact Prove2Me type adapters
and strict standard-axiom checks follow the upstream namespace.
-/

import Mathlib.Tactic.Common
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Multiplicity
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Multiplicity

/-!
# Odd Perfect Numbers: Euler's Form and Touchard's Congruence

This file proves two classical results about odd perfect numbers (OPNs):

1. **Euler's theorem (1747)**: every OPN has the form `n = p^k · m²` where `p` is prime,
   `p ≡ k ≡ 1 (mod 4)`, and `p ∤ m`.

2. **Touchard's congruence (1953)**: any OPN satisfies `n ≡ 1 (mod 12)` or `n ≡ 9 (mod 36)`.

`touchard_congruence` is unconditional: it invokes `euler_opn_form` internally.

## Main declarations

- `euler_opn_form`: Euler's 1747 theorem (machine-verified).
- `touchard_congruence`: Touchard's 1953 congruence (unconditional).
- `sigma_mul_of_coprime`, `opn_product_constraint`, `sigma_prime_pow_ratio`
- `v2_sigma_prime_power`, `v2_sigma_square_factor`

## LLM Assist

- This proof's development was supplemented & made possible by the utilization of LLM 

## References

- Touchard, J. (1953). *On prime numbers and perfect numbers*. Scripta Math. 19, 35–39.
- Euler, L. (1747). *De numeris perfectis*. Opera Omnia I.2, 86–162.
- Ochem, P. and Rao, M. (2012). *Odd perfect numbers are greater than 10^1500*.
  Math. Comp. 81, 1869–1877.
-/

open Nat ArithmeticFunction BigOperators

namespace Nat.ArithmeticFunction.OddPerfect

/-- `n` is perfect if the sum of all its divisors equals `2 * n`. -/
def Perfect (n : ℕ) : Prop := sigma 1 n = 2 * n

/-! ### 2-adic arithmetic helpers -/

private lemma pow_odd_of_odd {q : ℕ} (hq : q % 2 = 1) (i : ℕ) : q ^ i % 2 = 1 := by
  induction i with
  | zero => simp
  | succ n ih => simp [pow_succ, Nat.mul_mod, hq, ih]

private lemma pow_mod4_of_mod4 {p : ℕ} (hp : p % 4 = 1) (i : ℕ) : p ^ i % 4 = 1 := by
  induction i with
  | zero => simp
  | succ n ih => simp [pow_succ, Nat.mul_mod, hp, ih]

private lemma geom_sum_mod2 (q n : ℕ) (hq : q % 2 = 1) :
    (∑ i ∈ Finset.range n, q ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, pow_odd_of_odd hq k, ih]; omega

private lemma geom_sum_odd_mod2 (q e : ℕ) (hq : q % 2 = 1) :
    (∑ i ∈ Finset.range (2 * e + 1), q ^ i) % 2 = 1 := by
  have h := geom_sum_mod2 q (2 * e + 1) hq; omega

private lemma geom_sum_mod4 (p n : ℕ) (hp : p % 4 = 1) :
    (∑ i ∈ Finset.range n, p ^ i) % 4 = n % 4 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, pow_mod4_of_mod4 hp k, ih]; omega

private lemma geom_sum_mod4_eq2 (p n : ℕ) (hp : p % 4 = 1) (hn : n % 4 = 2) :
    (∑ i ∈ Finset.range n, p ^ i) % 4 = 2 := by
  have h := geom_sum_mod4 p n hp; omega

/-! ### 2-adic valuation -/

private noncomputable def v₂ (n : ℕ) : ℕ := (n.factorization) 2

private lemma v₂_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : v₂ (a * b) = v₂ a + v₂ b := by
  simp [v₂, Nat.factorization_mul ha hb, Finsupp.add_apply]

private lemma v₂_one : v₂ 1 = 0 := by simp [v₂]

private lemma v₂_two : v₂ 2 = 1 := by
  simp only [v₂]
  have h2prime : Nat.Prime 2 := by decide
  have h2dvd : 2 ^ 1 ∣ 2 := by norm_num
  have h4notdvd : ¬ 2 ^ 2 ∣ 2 := by norm_num
  apply Nat.le_antisymm
  · by_contra hlt
    push Not at hlt
    exact h4notdvd ((h2prime.pow_dvd_iff_le_factorization (by norm_num) (k := 2)).mpr (by omega))
  · exact (h2prime.pow_dvd_iff_le_factorization (by norm_num) (k := 1)).mp h2dvd

private lemma v₂_odd {n : ℕ} (hn : ¬ 2 ∣ n) (_hn_pos : n ≠ 0) : v₂ n = 0 :=
  Nat.factorization_eq_zero_of_not_dvd hn

private lemma v₂_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    v₂ (∏ i ∈ s, f i) = ∑ i ∈ s, v₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v₂_one]
  | insert a s has ih =>
    have ha : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert has, Finset.sum_insert has,
        v₂_mul ha (Finset.prod_ne_zero_iff.mpr hs), ih hs]

private lemma v2_eq_one_of_mod4_eq2 {n : ℕ} (hn : n % 4 = 2) : v₂ n = 1 := by
  have hpos : n ≠ 0 := by omega
  have h2prime : Nat.Prime 2 := by decide
  have h2dvd : 2 ^ 1 ∣ n := ⟨n / 2, by omega⟩
  have h4notdvd : ¬ (2 ^ 2 ∣ n) := by norm_num; intro ⟨k, hk⟩; omega
  simp only [v₂]
  apply Nat.le_antisymm
  · by_contra hlt
    push Not at hlt
    exact h4notdvd ((h2prime.pow_dvd_iff_le_factorization hpos (k := 2)).mpr (by omega))
  · exact (h2prime.pow_dvd_iff_le_factorization hpos (k := 1)).mp h2dvd

/-! ### Parity of σ(p^a) for odd primes -/

private lemma odd_prime_mod2 {p : ℕ} (hp : Nat.Prime p) (hp_odd : ¬ 2 ∣ p) : p % 2 = 1 := by
  have : p % 2 ≠ 0 := fun h => hp_odd ⟨p / 2, by omega⟩
  omega

private lemma pow_odd_prime_odd {p : ℕ} (hp : Nat.Prime p) (hp_odd : ¬ 2 ∣ p) (i : ℕ) :
    p ^ i % 2 = 1 :=
  pow_odd_of_odd (odd_prime_mod2 hp hp_odd) i

/-- For odd prime p, `σ(p^a) ≡ a+1 (mod 2)`. -/
lemma sigma_prime_pow_mod2 (p a : ℕ) (hp : Nat.Prime p) (hp_odd : ¬ 2 ∣ p) :
    sigma 1 (p ^ a) % 2 = (a + 1) % 2 := by
  induction a with
  | zero =>
    simp [sigma_apply, Nat.divisors_prime_pow hp]
  | succ k ih =>
    have h_sum_k1 : sigma 1 (p ^ (k + 1)) = ∑ i ∈ Finset.range (k + 2), p ^ i := by
      rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
    have h_sum_k : sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
      rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
    rw [h_sum_k1, show k + 2 = (k + 1) + 1 from rfl, Finset.sum_range_succ,
        Nat.add_mod, pow_odd_prime_odd hp hp_odd (k + 1), ← h_sum_k, ih]
    omega

/-- `2 ∣ σ(p^a)` iff `a` is odd (for odd prime p). -/
lemma sigma_prime_pow_two_dvd_iff (p a : ℕ) (hp : Nat.Prime p) (hp_odd : ¬ 2 ∣ p) :
    2 ∣ sigma 1 (p ^ a) ↔ a % 2 = 1 := by
  constructor
  · intro h2
    have h0 : sigma 1 (p ^ a) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
    have := sigma_prime_pow_mod2 p a hp hp_odd
    omega
  · intro ha
    rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod2 p a hp hp_odd]
    omega

/-! ### Mod-4 analysis -/

/-- If p ≡ 1 (mod 4), then p^i ≡ 1 (mod 4) for all i. -/
lemma pow_mod4_one {p : ℕ} (hp : p % 4 = 1) (i : ℕ) : p ^ i % 4 = 1 :=
  pow_mod4_of_mod4 hp i

private lemma pow_mod4_three (p i : ℕ) (hp : p % 4 = 3) :
    p ^ i % 4 = if i % 2 = 0 then 1 else 3 := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, hp, ih]
    split_ifs with h1 h2
    · omega
    · norm_num
    · norm_num
    · omega

private lemma sigma_prime_pow_mod4_zero_of_p3 (p k : ℕ) (hp : Nat.Prime p)
    (hp_mod4 : p % 4 = 3) (hk_odd : k % 2 = 1) : sigma 1 (p ^ k) % 4 = 0 := by
  obtain ⟨t, hk⟩ : ∃ t, k = 2 * t + 1 := ⟨k / 2, by omega⟩
  subst hk
  have h_sum_raw : sigma 1 (p ^ (2 * t + 1)) = ∑ i ∈ Finset.range (2 * t + 1 + 1), p ^ i := by
    rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
  have h_sum : sigma 1 (p ^ (2 * t + 1)) = ∑ i ∈ Finset.range (2 * t + 2), p ^ i := by
    simpa only [show 2 * t + 1 + 1 = 2 * t + 2 from by omega] using h_sum_raw
  rw [h_sum]; clear h_sum h_sum_raw hk_odd
  induction t with
  | zero =>
    simp only [mul_zero, zero_add, Finset.sum_range_succ, Finset.sum_range_zero,
               pow_zero, pow_one]
    omega
  | succ t ih =>
    have h_sq_mod4 : p ^ 2 % 4 = 1 := by
      rw [show p ^ 2 = p * p from by ring, Nat.mul_mod, hp_mod4]
    have hp_even : p ^ (2 * t + 2) % 4 = 1 := by
      rw [show p ^ (2 * t + 2) = (p ^ 2) ^ (t + 1) from by ring, Nat.pow_mod, h_sq_mod4]; simp
    have hp_odd : p ^ (2 * t + 3) % 4 = 3 := by
      rw [show 2 * t + 3 = 2 * t + 2 + 1 from by omega, pow_succ, Nat.mul_mod, hp_even, hp_mod4]
    rw [show 2 * (t + 1) + 2 = 2 * t + 2 + 1 + 1 from by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
    omega

private lemma sigma_prime_pow_mod4_of_p1 (p k : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 1) :
    sigma 1 (p ^ k) % 4 = (k + 1) % 4 := by
  induction k with
  | zero => simp [sigma_apply, Nat.divisors_prime_pow hp]
  | succ n ih =>
    have h_sum_n1 : sigma 1 (p ^ (n + 1)) = ∑ i ∈ Finset.range (n + 2), p ^ i := by
      rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
    have h_sum_n : sigma 1 (p ^ n) = ∑ i ∈ Finset.range (n + 1), p ^ i := by
      rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
    rw [h_sum_n1, show n + 2 = (n + 1) + 1 from rfl, Finset.sum_range_succ, Nat.add_mod,
        pow_mod4_of_mod4 hp_mod4 (n + 1), ← h_sum_n, ih]
    omega

/-! ### σ multiplicativity, product equation, prime-power ratio -/

/-- The sum-of-divisors function is multiplicative. -/
lemma sigma_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

/-- The fundamental OPN product equation. -/
theorem opn_product_constraint {p k m : ℕ}
    (hperf : Perfect (p ^ k * m ^ 2))
    (hcop : Nat.Coprime (p ^ k) (m ^ 2)) :
    sigma 1 (p ^ k) * sigma 1 (m ^ 2) = 2 * (p ^ k * m ^ 2) := by
  rw [← sigma_mul_of_coprime hcop]; exact hperf

/-- The sigma prime-power ratio identity: `σ(p^k) · (p - 1) + 1 = p^(k+1)`. -/
lemma sigma_prime_pow_ratio (p k : ℕ) (hp : Nat.Prime p) :
    sigma 1 (p ^ k) * (p - 1) + 1 = p ^ (k + 1) := by
  have h_sum : sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
  rw [h_sum]
  zify [hp.one_le, Nat.one_le_pow (k + 1) p hp.pos]
  linarith [geom_sum_mul (p : ℤ) (k + 1)]

/-- Strict version: `σ(p^k) · (p - 1) < p^(k+1)`. -/
lemma sigma_prime_pow_lt (p k : ℕ) (hp : Nat.Prime p) :
    sigma 1 (p ^ k) * (p - 1) < p ^ (k + 1) := by
  have h := sigma_prime_pow_ratio p k hp; omega

/-- Any OPN in Euler form is ≡ 1 (mod 4). -/
lemma opn_mod4 (p k m : ℕ) (h_odd : ¬ 2 ∣ p ^ k * m ^ 2) (hp_mod : p % 4 = 1) :
    (p ^ k * m ^ 2) % 4 = 1 := by
  have hm_odd : m % 2 = 1 := by
    by_contra hm
    push Not at hm
    exact h_odd (Dvd.dvd.mul_left (Dvd.dvd.pow (by omega : 2 ∣ m) (by norm_num)) (p ^ k))
  have hpk_mod : p ^ k % 4 = 1 := pow_mod4_of_mod4 hp_mod k
  have hm2_mod : m ^ 2 % 4 = 1 := by
    have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hm4 with h | h <;> simp [pow_succ, pow_zero, Nat.mul_mod, h]
  calc (p ^ k * m ^ 2) % 4
      = (p ^ k % 4 * (m ^ 2 % 4)) % 4 := by rw [Nat.mul_mod]
    _ = (1 * 1) % 4 := by rw [hpk_mod, hm2_mod]
    _ = 1 := by norm_num

/-! ### σ over factorization -/

private lemma prime_of_mem_factorization_support {n p : ℕ}
    (h : p ∈ (Nat.factorization n).support) : Nat.Prime p :=
  Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])

private lemma sigma_prod_factorization (n : ℕ) (hn : n ≠ 0) :
    sigma 1 n = ∏ p ∈ (Nat.factorization n).support,
      sigma 1 (p ^ ((Nat.factorization n) p)) :=
  isMultiplicative_sigma.multiplicative_factorization _ hn

private lemma sigma_prime_pow_ne_zero (p a : ℕ) (hp : Nat.Prime p) : sigma 1 (p ^ a) ≠ 0 := by
  have hpa : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  have : 0 < sigma 1 (p ^ a) := sigma_pos 1 (p ^ a) hpa
  omega

private lemma v2_sigma_odd_perfect (n : ℕ) (h_odd : ¬ 2 ∣ n) (h_perf : Perfect n)
    (hn_pos : n ≠ 0) : v₂ (sigma 1 n) = 1 := by
  rw [h_perf, v₂_mul (by omega) hn_pos, v₂_two, v₂_odd h_odd hn_pos]

private lemma hf_sigma_factorization (n : ℕ) (hn : n ≠ 0) (p : ℕ)
    (hp : p ∈ (Nat.factorization n).support) :
    sigma 1 (p ^ ((Nat.factorization n) p)) ≠ 0 :=
  sigma_prime_pow_ne_zero p _ (prime_of_mem_factorization_support hp)

/-! ### 2-adic valuation at prime powers -/

private lemma v2_sigma_prime_pow_ge_two_p3 (p a : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 3)
    (ha_odd : a % 2 = 1) : 2 ≤ v₂ (sigma 1 (p ^ a)) := by
  have hmod4 : sigma 1 (p ^ a) % 4 = 0 :=
    sigma_prime_pow_mod4_zero_of_p3 p a hp hp_mod4 ha_odd
  have hpos : sigma 1 (p ^ a) ≠ 0 := sigma_prime_pow_ne_zero p a hp
  have h4dvd : 4 ∣ sigma 1 (p ^ a) := Nat.dvd_of_mod_eq_zero hmod4
  have h4dvd' : 2 ^ 2 ∣ sigma 1 (p ^ a) := by simpa [show (2 : ℕ) ^ 2 = 4 from by norm_num]
  exact ((by decide : Nat.Prime 2).pow_dvd_iff_le_factorization hpos).mp h4dvd'

private lemma v2_sigma_prime_pow_p3_even (p a : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 3)
    (ha_even : a % 2 = 0) : v₂ (sigma 1 (p ^ a)) = 0 := by
  have hp_odd : ¬ 2 ∣ p := by
    intro h2; have := (hp.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)
    rw [← this] at hp_mod4; norm_num at hp_mod4
  have h_odd_sigma : ¬ 2 ∣ sigma 1 (p ^ a) := by
    rw [sigma_prime_pow_two_dvd_iff p a hp hp_odd]; omega
  exact v₂_odd h_odd_sigma (sigma_prime_pow_ne_zero p a hp)

private lemma v2_sigma_prime_pow_p1_a1 (p a : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 1)
    (ha_mod4 : a % 4 = 1) : v₂ (sigma 1 (p ^ a)) = 1 :=
  v2_eq_one_of_mod4_eq2 (by have h := sigma_prime_pow_mod4_of_p1 p a hp hp_mod4; rw [h]; omega)

private lemma v2_sigma_prime_pow_p1_a3 (p a : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 1)
    (ha_mod4 : a % 4 = 3) : 2 ≤ v₂ (sigma 1 (p ^ a)) := by
  have hpos : sigma 1 (p ^ a) ≠ 0 := sigma_prime_pow_ne_zero p a hp
  have hmod4 : sigma 1 (p ^ a) % 4 = 0 := by
    have h := sigma_prime_pow_mod4_of_p1 p a hp hp_mod4; rw [h]; omega
  have h4dvd' : 2 ^ 2 ∣ sigma 1 (p ^ a) := by
    simpa [show (2 : ℕ) ^ 2 = 4 from by norm_num] using Nat.dvd_of_mod_eq_zero hmod4
  exact ((by decide : Nat.Prime 2).pow_dvd_iff_le_factorization hpos).mp h4dvd'

private lemma v2_sigma_prime_pow_p1_even (p a : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 1)
    (ha_even : a % 2 = 0) : v₂ (sigma 1 (p ^ a)) = 0 := by
  have hp_odd : ¬ 2 ∣ p := by
    intro h2; have := (hp.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)
    rw [← this] at hp_mod4; norm_num at hp_mod4
  have h_odd_sigma : ¬ 2 ∣ sigma 1 (p ^ a) := by
    rw [sigma_prime_pow_two_dvd_iff p a hp hp_odd]; omega
  exact v₂_odd h_odd_sigma (sigma_prime_pow_ne_zero p a hp)

/-- For `p ≡ k ≡ 1 (mod 4)`, `v₂(σ(p^k)) = 1`. -/
lemma v2_sigma_prime_power (p k : ℕ) (hp : Nat.Prime p) (_hp_odd : ¬ 2 ∣ p)
    (hp_mod : p % 4 = 1) (hk_mod : k % 4 = 1) : v₂ (sigma 1 (p ^ k)) = 1 :=
  v2_sigma_prime_pow_p1_a1 p k hp hp_mod hk_mod

/-- For odd prime `q`, `v₂(σ(q^(2e))) = 0`. -/
lemma v2_sigma_square_factor (q e : ℕ) (hq : Nat.Prime q) (hq_odd : ¬ 2 ∣ q) :
    v₂ (sigma 1 (q ^ (2 * e))) = 0 := by
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
    have hq2 : q % 2 = 1 := odd_prime_mod2 hq hq_odd; omega
  rcases hq4 with h | h
  · exact v2_sigma_prime_pow_p1_even q (2 * e) hq h (by omega)
  · exact v2_sigma_prime_pow_p3_even q (2 * e) hq h (by omega)

/-! ### Euler's theorem (1747) -/

/-- **Euler's theorem (1747)**.
Every odd perfect number `n` has the form `n = p^k · m²` with `p` prime,
`p ≡ 1 (mod 4)`, `k ≡ 1 (mod 4)`, and `p ∤ m`. -/
theorem euler_opn_form (n : ℕ) (h_odd : ¬ 2 ∣ n) (h_perf : Perfect n) :
    ∃ (p k m : ℕ),
      Nat.Prime p ∧ n = p ^ k * m ^ 2 ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m := by
  have hn_pos : n ≠ 0 := fun h => h_odd (h ▸ dvd_zero 2)
  have hv₂_sigma_n : v₂ (sigma 1 n) = 1 := v2_sigma_odd_perfect n h_odd h_perf hn_pos
  have h_sigma_fact : v₂ (∏ p ∈ (Nat.factorization n).support,
      sigma 1 (p ^ ((Nat.factorization n) p))) = 1 := by
    rw [← sigma_prod_factorization n hn_pos, hv₂_sigma_n]
  have h_v2_sum : ∑ p ∈ (Nat.factorization n).support,
      v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1 := by
    rw [← v₂_prod _ _ (hf_sigma_factorization n hn_pos), h_sigma_fact]
  -- Exactly one prime p in the factorization has v₂(σ(p^a_p)) = 1
  have h_unique : ∃! p ∈ (Nat.factorization n).support,
      v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1 := by
    have h_card : (Finset.filter (fun p =>
        v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1)
        (Nat.factorization n).support).card = 1 := by
      have : ∀ p ∈ (Nat.factorization n).support,
          v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) ≤ 1 := by
        intro p hp
        by_contra! hgt
        have := Finset.single_le_sum (f := fun p => v₂ (sigma 1 (p ^ ((Nat.factorization n) p))))
          (by intro q _; exact Nat.zero_le _) hp
        linarith [h_v2_sum]
      have h1 : (∑ p ∈ Finset.filter (fun p =>
          v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1)
          (Nat.factorization n).support, 1) = 1 := by
        calc _ = ∑ p ∈ (Nat.factorization n).support,
              if v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1 then 1 else 0 :=
            Finset.sum_filter _ _
          _ = ∑ p ∈ (Nat.factorization n).support,
              v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hle := this p hp
            by_cases hv : v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1
            · simp [hv]
            · have : v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 0 := by omega
              simp [this]
          _ = 1 := h_v2_sum
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
      exact h1
    rcases Finset.card_eq_one.mp h_card with ⟨p, hp_eq⟩
    have hp_filter : p ∈ Finset.filter (fun p =>
        v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1)
        (Nat.factorization n).support :=
      hp_eq ▸ Finset.mem_singleton_self p
    have hp_mem : p ∈ (Nat.factorization n).support := (Finset.mem_filter.mp hp_filter).1
    have hp_val1 : v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1 :=
      (Finset.mem_filter.mp hp_filter).2
    refine ⟨p, ⟨hp_mem, hp_val1⟩, fun q ⟨hq_mem, hq_val1⟩ => ?_⟩
    by_contra hne
    have hq_in_filter : q ∈ Finset.filter (fun p =>
        v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1)
        (Nat.factorization n).support :=
      Finset.mem_filter.mpr ⟨hq_mem, hq_val1⟩
    have hp_in_filter : p ∈ Finset.filter (fun p =>
        v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1)
        (Nat.factorization n).support :=
      Finset.mem_filter.mpr ⟨hp_mem, hp_val1⟩
    have h2 : ({p, q} : Finset ℕ) ⊆ Finset.filter (fun p =>
        v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1)
        (Nat.factorization n).support := by
      intro x hx; simp at hx; rcases hx with rfl | rfl
      · exact hp_in_filter
      · exact hq_in_filter
    have h3 : 2 ≤ (Finset.filter (fun p =>
        v₂ (sigma 1 (p ^ ((Nat.factorization n) p))) = 1)
        (Nat.factorization n).support).card := by
      calc 2 = ({p, q} : Finset ℕ).card := (Finset.card_pair (Ne.symm hne)).symm
        _ ≤ _ := Finset.card_le_card h2
    rw [h_card] at h3; omega
  rcases h_unique with ⟨p, ⟨hp_mem, hp_val1⟩, hp_unique⟩
  have hp_prime : Nat.Prime p := prime_of_mem_factorization_support hp_mem
  -- p ≡ 1 (mod 4)
  have hp_mod4 : p % 4 = 1 := by
    have hp_odd : ¬ 2 ∣ p := by
      intro h2
      exact h_odd ((hp_prime.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num) ▸
        Nat.dvd_of_factorization_pos (Finsupp.mem_support_iff.mp hp_mem))
    have : p % 4 = 1 ∨ p % 4 = 3 := by have := odd_prime_mod2 hp_prime hp_odd; omega
    rcases this with h | h
    · exact h
    · rcases Nat.even_or_odd ((Nat.factorization n) p) with ⟨_, heven⟩ | ⟨_, hodd⟩
      · linarith [v2_sigma_prime_pow_p3_even p ((Nat.factorization n) p) hp_prime h (by omega),
                  hp_val1.symm.le]
      · linarith [v2_sigma_prime_pow_ge_two_p3 p ((Nat.factorization n) p) hp_prime h (by omega),
                  hp_val1.symm.le]
  -- a_p ≡ 1 (mod 4)
  let a_p := (Nat.factorization n) p
  have ha_p_mod4 : a_p % 4 = 1 := by
    rcases Nat.even_or_odd a_p with ⟨_, heven⟩ | ⟨_, hodd⟩
    · linarith [v2_sigma_prime_pow_p1_even p a_p hp_prime hp_mod4 (by omega),
                hp_val1.symm.le]
    · have : a_p % 4 = 1 ∨ a_p % 4 = 3 := by omega
      rcases this with h | h
      · exact h
      · linarith [v2_sigma_prime_pow_p1_a3 p a_p hp_prime hp_mod4 h, hp_val1.symm.le]
  -- All other prime factors have even exponent
  have all_others_even : ∀ q ∈ (Nat.factorization n).support, q ≠ p →
      ((Nat.factorization n) q) % 2 = 0 := by
    intro q hq_mem hq_ne
    have hq_prime : Nat.Prime q := prime_of_mem_factorization_support hq_mem
    have hq_odd : ¬ 2 ∣ q := by
      intro h2
      exact h_odd ((hq_prime.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num) ▸
        Nat.dvd_of_factorization_pos (Finsupp.mem_support_iff.mp hq_mem))
    have hq_val : v₂ (sigma 1 (q ^ ((Nat.factorization n) q))) = 0 := by
      have hq_le1 : v₂ (sigma 1 (q ^ ((Nat.factorization n) q))) ≤ 1 := by
        by_contra! hgt
        have := Finset.single_le_sum
          (f := fun r => v₂ (sigma 1 (r ^ ((Nat.factorization n) r))))
          (by intro r _; exact Nat.zero_le _) hq_mem
        linarith [h_v2_sum]
      rcases Nat.eq_zero_or_pos (v₂ (sigma 1 (q ^ ((Nat.factorization n) q)))) with h | h
      · exact h
      · have hv1 : v₂ (sigma 1 (q ^ ((Nat.factorization n) q))) = 1 := by omega
        exact absurd (hp_unique q ⟨hq_mem, hv1⟩) hq_ne
    have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by have := odd_prime_mod2 hq_prime hq_odd; omega
    rcases Nat.even_or_odd ((Nat.factorization n) q) with ⟨_, heven⟩ | ⟨_, hodd⟩
    · omega
    · rcases hq4 with hq4 | hq4
      · have hmod4_cases : ((Nat.factorization n) q) % 4 = 1 ∨
            ((Nat.factorization n) q) % 4 = 3 := by omega
        rcases hmod4_cases with h | h
        · linarith [v2_sigma_prime_pow_p1_a1 q _ hq_prime hq4 h, hq_val.symm.le]
        · linarith [v2_sigma_prime_pow_p1_a3 q _ hq_prime hq4 h, hq_val.symm.le]
      · linarith [v2_sigma_prime_pow_ge_two_p3 q ((Nat.factorization n) q) hq_prime hq4 (by omega), hq_val.symm.le]
  -- Construct m
  have hn_fact : n = p ^ a_p * ∏ q ∈ ((Nat.factorization n).support.erase p),
      q ^ ((Nat.factorization n) q) := by
    calc n = ∏ r ∈ (Nat.factorization n).support, r ^ ((Nat.factorization n) r) :=
          (Nat.prod_factorization_pow_eq_self hn_pos).symm
      _ = p ^ a_p * ∏ q ∈ ((Nat.factorization n).support.erase p),
          q ^ ((Nat.factorization n) q) := by
        rw [← Finset.mul_prod_erase _ _ hp_mem]
  let m := ∏ q ∈ ((Nat.factorization n).support.erase p), q ^ (((Nat.factorization n) q) / 2)
  have hm_sq : m ^ 2 = ∏ q ∈ ((Nat.factorization n).support.erase p),
      q ^ ((Nat.factorization n) q) := by
    rw [show m = ∏ q ∈ ((Nat.factorization n).support.erase p),
        q ^ (((Nat.factorization n) q) / 2) from rfl, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun q hq => ?_
    have ha := all_others_even q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)
    rw [← pow_mul]
    congr 1; omega
  have hn_eq : n = p ^ a_p * m ^ 2 := by rw [hm_sq]; exact hn_fact
  have hp_not_dvd_m : ¬ p ∣ m := by
    intro hp_dvd
    rcases (hp_prime.prime.dvd_finsetProd_iff _).mp hp_dvd with ⟨q, hq, hp_dvd_qpow⟩
    have hp_dvd_q := hp_prime.dvd_of_dvd_pow hp_dvd_qpow
    have hq_prime := prime_of_mem_factorization_support (Finset.mem_of_mem_erase hq)
    have : p = q := (hq_prime.eq_one_or_self_of_dvd p hp_dvd_q).resolve_left hp_prime.one_lt.ne'
    exact Finset.ne_of_mem_erase hq this.symm
  exact ⟨p, a_p, m, hp_prime, hn_eq, hp_mod4, ha_p_mod4, hp_not_dvd_m⟩

end Nat.ArithmeticFunction.OddPerfect

private theorem natPerfect_to_upstreamPerfect (n : ℕ) (hn : Nat.Perfect n) :
    Nat.ArithmeticFunction.OddPerfect.Perfect n := by
  change ArithmeticFunction.sigma 1 n = 2 * n
  rw [ArithmeticFunction.sigma_one_apply]
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).mp hn

/-- Exact Prove2Me target ce498e6e-9abd-42ab-98a6-b7d54a53b45f.
Compatibility adaptation of umpolungfish's public-domain Euler-form proof. -/
theorem solution (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    ∃ p k m : ℕ, p.Prime ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m ∧
      n = p ^ k * m ^ 2 := by
  obtain ⟨p, k, m, hp, hn_eq, hp_mod, hk_mod, hcop⟩ :=
    Nat.ArithmeticFunction.OddPerfect.euler_opn_form n hodd.not_two_dvd_nat
      (natPerfect_to_upstreamPerfect n hn)
  exact ⟨p, k, m, hp, hp_mod, hk_mod, hcop, hn_eq⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
