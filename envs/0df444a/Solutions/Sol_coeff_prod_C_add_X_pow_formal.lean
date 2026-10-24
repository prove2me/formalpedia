-- Prove2me | solution 1 for coeff_prod_C_add_X_pow_formal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:32:04.831998+00:00
-- url     : https://prove2.me/submissions/cf881298-c8be-4ac8-a669-d0bfcdd8522a

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Complex.Basic

open MvPolynomial in
theorem solution
    {m : ℕ} (a : Fin m → ℕ) (A : Fin m →₀ ℕ) (c : PowerSeries ℂ) :
    MvPolynomial.coeff A
      (∏ i : Fin m, (MvPolynomial.C c + MvPolynomial.X i) ^ a i :
        MvPolynomial (Fin m) (PowerSeries ℂ)) =
      PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        c ^ (∑ i : Fin m, (a i - A i)) := by
  classical
  set g : Fin m → ℕ → PowerSeries ℂ := fun i k => c ^ (a i - k) * ((a i).choose k : PowerSeries ℂ)
  have h1 : ∀ i, (C c + X i : MvPolynomial (Fin m) (PowerSeries ℂ)) ^ (a i) =
      ∑ k ∈ Finset.range (a i + 1), monomial (Finsupp.single i k) (g i k) := by
    intro i
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g, X_pow_eq_monomial, ← C_pow, C_mul_monomial]
    rw [← map_natCast (C : PowerSeries ℂ →+* MvPolynomial (Fin m) (PowerSeries ℂ))]
    rw [mul_assoc, ← map_mul, mul_comm, C_mul_monomial, mul_one]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum]
  simp_rw [← monomial_sum_prod, coeff_sum, coeff_monomial]
  have hfs : ∀ κ : Fin m → ℕ, (∑ i, Finsupp.single i (κ i) = A) ↔ κ = ⇑A := by
    intro κ
    constructor
    · rintro h; funext i; rw [← h]; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · rintro rfl; ext j; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp_rw [hfs]
  rw [Finset.sum_ite_eq']
  split_ifs with hA
  · simp only [g, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [mul_comm]; congr 1
    simp
  · have : ∃ i, a i < A i := by
      by_contra h; push Not at h
      exact hA (Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (h i)))
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (Nat.choose_eq_zero_of_lt hi)]
    simp

