-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_odd_local_p_valuation_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T00:15:31.931544+00:00
-- url     : https://prove2.me/submissions/57d19ef2-2f44-4aa1-aba8-1e643ee59072

-- Proof draft for PENDING five_odd_local_p_valuation_source. HELD until PUBLISHED.
-- Route: valuation-sum (= 5, odd) + finite-set parity by Finset induction.
-- Imports only Proved theorems (valuation-sum 62ad4aeb).
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_five_p_valuation_sum_eq_five

theorem solution (p m s : Nat)
    (hp : p.Prime)
    (hm0 : m != 0)
    (hps : Not (Dvd.dvd p s))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    exists t : Nat, t ∈ m.primeFactors /\
      Not (Even (((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) p)) := by
  have hsum := OddPerfectNumber.Kernel.five_p_valuation_sum_eq_five
    p m s hp hm0 hps h2
  have hodd : Not (Even (∑ t ∈ m.primeFactors,
      (((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) p))) := by
    rw [hsum]
    decide
  have gen : ∀ T : Finset Nat,
      (∀ t ∈ T, Even ((((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) p))) →
      Even (∑ t ∈ T, ((((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) p))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert x T hx ih =>
        intro hT
        rw [Finset.sum_insert hx]
        apply Even.add
        · exact hT x (Finset.mem_insert_self x T)
        · apply ih
          intro y hy
          exact hT y (Finset.mem_insert_of_mem hy)
  by_contra hn
  have hall : ∀ t ∈ m.primeFactors,
      Even ((((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) p)) := by
    intro t ht
    by_contra hnot
    exact hn ⟨t, ht, hnot⟩
  exact hodd (gen _ hall)
