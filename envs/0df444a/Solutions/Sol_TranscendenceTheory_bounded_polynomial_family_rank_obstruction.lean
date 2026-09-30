-- Prove2me | solution 1 for TranscendenceTheory.bounded_polynomial_family_rank_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T18:28:02.868737+00:00
-- url     : https://prove2.me/submissions/c8be9ab6-912a-4cd0-b50d-be474163101c

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations

open scoped BigOperators

private theorem finite_family_rank_obstruction
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (A : Matrix α ι K) (B : Matrix α κ K) :
    (∃ k, ¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a k) ↔
      A.rank < (Matrix.fromCols A B).rank := by
  classical
  let S := Submodule.span K (Set.range A.col)
  let T := Submodule.span K (Set.range (Matrix.fromCols A B).col)
  have hST : S ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hB (k : κ) : B.col k ∈ S ↔
      ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a k := by
    rw [Submodule.mem_span_range_iff_exists_fun K]
    apply exists_congr
    intro u
    rw [funext_iff]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, mul_comm]
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  change (∃ k, ¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a k) ↔
    Module.finrank K S < Module.finrank K T
  constructor
  · rintro ⟨k, hk⟩
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne hST ?_
    intro heq
    apply hk
    apply (hB k).mp
    rw [heq]
    exact Submodule.subset_span ⟨Sum.inr k, rfl⟩
  · intro hrank
    by_contra hnone
    have hTS : T ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i | k, rfl⟩
      · exact Submodule.subset_span ⟨i, rfl⟩
      · apply (hB k).mpr
        by_contra hk
        exact hnone ⟨k, hk⟩
    exact (not_lt_of_ge (Submodule.finrank_mono hTS)) hrank

theorem solution
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (d : ℕ) (A : α → ι → Polynomial K) (B : α → κ → Polynomial K)
    (hA : ∀ a i, (A a i).natDegree ≤ d)
    (hB : ∀ a k, (B a k).natDegree ≤ d) :
    (∃ k, ¬ ∃ u : ι → K, ∀ a, ∑ i, Polynomial.C (u i) * A a i = B a k) ↔
      let Ac : Matrix (α × Fin (d + 1)) ι K := fun e i => (A e.1 i).coeff e.2.val
      let Bc : Matrix (α × Fin (d + 1)) κ K := fun e k => (B e.1 k).coeff e.2.val
      Ac.rank < (Matrix.fromCols Ac Bc).rank := by
  classical
  let Ac : Matrix (α × Fin (d + 1)) ι K := fun e i => (A e.1 i).coeff e.2.val
  let Bc : Matrix (α × Fin (d + 1)) κ K := fun e k => (B e.1 k).coeff e.2.val
  have hsol (k : κ) :
      (∃ u : ι → K, ∀ a, ∑ i, Polynomial.C (u i) * A a i = B a k) ↔
      (∃ u : ι → K, ∀ e, ∑ i, Ac e i * u i = Bc e k) := by
    apply exists_congr
    intro u
    constructor
    · intro hu e
      have h := congrArg (fun p : Polynomial K => p.coeff e.2.val) (hu e.1)
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at h
      simpa only [Ac, Bc, mul_comm] using h
    · intro hu a
      ext n
      by_cases hn : n ≤ d
      · simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
        simpa only [Ac, Bc, mul_comm] using hu (a, ⟨n, Nat.lt_succ_of_le hn⟩)
      · have hn' : d < n := Nat.lt_of_not_ge hn
        have hzero (i : ι) : (A a i).coeff n = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt ((hA a i).trans_lt hn')
        have hbzero : (B a k).coeff n = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt ((hB a k).trans_lt hn')
        simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
          hzero, mul_zero, Finset.sum_const_zero, hbzero]
  exact (exists_congr fun k => not_congr (hsol k)).trans
    (finite_family_rank_obstruction K (α × Fin (d + 1)) ι κ Ac Bc)
