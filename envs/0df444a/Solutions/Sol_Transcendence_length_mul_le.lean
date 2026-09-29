-- Prove2me | solution 1 for Transcendence.length_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:44:32.199721+00:00
-- url     : https://prove2.me/submissions/e8591582-b577-4781-8817-4024449831c8

import Mathlib

/-!
For a size function `ν : R → ℕ` on a semiring `R` and `p ∈ R[X]`, let `λ_ν(p) = ∑ₙ ν(pₙ)`, the
sum running over the support of `p`. The length of `P ∈ ℤ[X][Y]` is `λ_{λ_ν}(P)` with `ν = |·|`.

Suppose `ν(0) = 0`, `ν(a + b) ≤ ν(a) + ν(b)` and `ν(ab) ≤ ν(a)ν(b)`. Then `λ_ν` has the same three
properties.
* Subadditivity holds termwise, once both sides are summed over the union of the two supports.
* For the product, let `p̂ ∈ ℕ[X]` be the polynomial with coefficients `ν(pₙ)`, so that
  `λ_ν(p) = p̂(1)`. Since `(pq)ₙ = ∑_{i+j=n} pᵢqⱼ`, we get
  `ν((pq)ₙ) ≤ ∑_{i+j=n} ν(pᵢ)ν(qⱼ) = (p̂q̂)ₙ`, and summing over `n`,
  `λ_ν(pq) ≤ (p̂q̂)(1) = p̂(1)q̂(1) = λ_ν(p)λ_ν(q)`.

Starting from `ν = |·|` on `ℤ`, this gives the one-variable statement on `ℤ[X]`; applied again to
`ν = λ_{|·|}` on `ℤ[X]`, it gives the statement on `ℤ[X][Y]`.
-/

namespace S7W3_length_mul_le

open Polynomial

variable {R : Type*} [Semiring R]

/-- The sum of the sizes of the coefficients of `p`. -/
def lam (ν : R → ℕ) (p : R[X]) : ℕ :=
  ∑ n ∈ p.support, ν (p.coeff n)

theorem lam_zero (ν : R → ℕ) : lam ν 0 = 0 := by
  rw [lam, support_zero, Finset.sum_empty]

/-- The sum may run over any finset containing the support. -/
theorem lam_eq_sum (ν : R → ℕ) (hν : ν 0 = 0) (p : R[X]) {s : Finset ℕ} (hs : p.support ⊆ s) :
    lam ν p = ∑ n ∈ s, ν (p.coeff n) :=
  Finset.sum_subset hs fun n _ hn => by rw [notMem_support_iff.1 hn, hν]

theorem lam_add_le (ν : R → ℕ) (hν : ν 0 = 0) (hadd : ∀ a b, ν (a + b) ≤ ν a + ν b)
    (p q : R[X]) : lam ν (p + q) ≤ lam ν p + lam ν q := by
  classical
  rw [lam_eq_sum ν hν (p + q) support_add, lam_eq_sum ν hν p Finset.subset_union_left,
    lam_eq_sum ν hν q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun n _ => by
    rw [coeff_add]
    exact hadd _ _

/-- The polynomial with natural coefficients `ν(pₙ)`. -/
noncomputable def hat (ν : R → ℕ) (p : R[X]) : ℕ[X] :=
  ∑ n ∈ p.support, monomial n (ν (p.coeff n))

theorem coeff_hat (ν : R → ℕ) (hν : ν 0 = 0) (p : R[X]) (n : ℕ) :
    (hat ν p).coeff n = ν (p.coeff n) := by
  classical
  simp only [hat, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, hν]

theorem eval_one_hat (ν : R → ℕ) (p : R[X]) : (hat ν p).eval 1 = lam ν p := by
  simp only [hat, eval_finsetSum, eval_monomial, one_pow, mul_one, lam]

theorem lam_mul_le (ν : R → ℕ) (hν : ν 0 = 0) (hadd : ∀ a b, ν (a + b) ≤ ν a + ν b)
    (hmul : ∀ a b, ν (a * b) ≤ ν a * ν b) (p q : R[X]) :
    lam ν (p * q) ≤ lam ν p * lam ν q := by
  rw [← eval_one_hat ν p, ← eval_one_hat ν q, ← eval_mul, eval_eq_sum, sum_def, lam]
  simp only [one_pow, mul_one]
  calc ∑ n ∈ (p * q).support, ν ((p * q).coeff n)
      ≤ ∑ n ∈ (p * q).support, (hat ν p * hat ν q).coeff n := Finset.sum_le_sum fun n _ => ?_
    _ ≤ ∑ n ∈ (hat ν p * hat ν q).support, (hat ν p * hat ν q).coeff n :=
      Finset.sum_le_sum_of_ne_zero fun n _ hn => mem_support_iff.2 hn
  rw [coeff_mul, coeff_mul]
  refine (Finset.le_sum_of_subadditive ν hν.le hadd _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [coeff_hat ν hν, coeff_hat ν hν]
  exact hmul _ _

end S7W3_length_mul_le

open S7W3_length_mul_le in
theorem solution (P Q : Polynomial (Polynomial ℤ)) :
    ∑ k ∈ (P * Q).support, ∑ i ∈ ((P * Q).coeff k).support, (((P * Q).coeff k).coeff i).natAbs ≤
      (∑ k ∈ P.support, ∑ i ∈ (P.coeff k).support, ((P.coeff k).coeff i).natAbs) *
        ∑ k ∈ Q.support, ∑ i ∈ (Q.coeff k).support, ((Q.coeff k).coeff i).natAbs := by
  exact lam_mul_le (lam Int.natAbs) (lam_zero Int.natAbs)
    (lam_add_le Int.natAbs Int.natAbs_zero Int.natAbs_add_le)
    (lam_mul_le Int.natAbs Int.natAbs_zero Int.natAbs_add_le fun a b => (Int.natAbs_mul a b).le)
    P Q

#print axioms solution
