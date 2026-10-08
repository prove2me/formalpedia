-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_p_valuation_sum_eq_five
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:03:52.515993+00:00
-- url     : https://prove2.me/submissions/38162720-8fd9-4e15-9b96-4b4c1c6fa750

-- Proof draft for PENDING five_p_valuation_sum_eq_five. HELD until PUBLISHED.
-- Route: sigma-product rewrite; every local divisor sum is nonzero (1 is a divisor
-- of each positive prime power, single_le_sum); Nat.factorization_prod turns the
-- product into a Finsupp sum, evaluated at p via the reference congrArg+finsetSum
-- pattern; the right side is 5 by the prime-power helper. Imports only Proved theorems.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_sum_divisors_eq_prod_prime_pow
import Theorems.Thm_OddPerfectNumber_Kernel_factorization_p_of_mul_prime_pow_ne

theorem solution (p m s : Nat)
    (hp : p.Prime)
    (hm0 : m != 0)
    (hps : Not (Dvd.dvd p s))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    ∑ t ∈ m.primeFactors,
      ((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p) = 5 := by
  have hprod := OddPerfectNumber.Kernel.sum_divisors_eq_prod_prime_pow (m := m) hm0
  have hne : ∀ t ∈ m.primeFactors,
      (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) ≠ 0 := by
    intro t ht
    have htp : t.Prime := Nat.prime_of_mem_primeFactors ht
    have hte : t ^ (2 * m.factorization t) ≠ 0 := pow_ne_zero _ htp.ne_zero
    have h1 : (1 : Nat) ∈ (t ^ (2 * m.factorization t)).divisors :=
      Nat.mem_divisors.mpr ⟨one_dvd _, hte⟩
    have hle := Finset.single_le_sum (fun d _ => Nat.zero_le d) h1
    omega
  have hF : (∏ t ∈ m.primeFactors,
      (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d)).factorization
      = ∑ t ∈ m.primeFactors,
        ((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) :=
    Nat.factorization_prod hne
  have hFp : ((∏ t ∈ m.primeFactors,
      (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d)).factorization) p
      = ∑ t ∈ m.primeFactors,
        (((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) p) := by
    have heval := congrArg (fun f : Nat →₀ Nat => f p) hF
    simpa only [Finsupp.finsetSum_apply] using heval
  have hsg : ((∑ d ∈ (m ^ 2).divisors, d).factorization) p = 5 := by
    rw [h2]
    exact OddPerfectNumber.Kernel.factorization_p_of_mul_prime_pow_ne hp hps
  rw [← hFp, ← hprod]
  exact hsg
