-- Prove2me | solution 1 for TranscendenceTheory.truncated_geometric_rank_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T20:18:21.150986+00:00
-- url     : https://prove2.me/submissions/964f72ed-86c6-4d3a-b716-698570a459da

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

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

private lemma weighted_poly_coeff
    {K ι : Type*} [CommRing K] [Fintype ι]
    (P : Polynomial K) (V : ι → Polynomial K) (u : ι → K) (n : ℕ) :
    (P * ∑ i, Polynomial.C (u i) * V i).coeff n =
      ∑ i, (P * V i).coeff n * u i := by
  classical
  rw [Finset.mul_sum]
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show P * (Polynomial.C (u i) * V i) = Polynomial.C (u i) * (P * V i) by ring]
  rw [Polynomial.coeff_C_mul]
  exact mul_comm _ _

private lemma truncated_poly_system_iff
    (K α ι : Type*) [Field K] [Fintype ι]
    (s : ℕ) (P : Polynomial K) (V : α → ι → Polynomial K) (B : α → Polynomial K) :
    (∃ u : ι → K, ∀ a,
      Polynomial.X ^ (s + 1) ∣ P * (∑ i, Polynomial.C (u i) * V a i) - B a) ↔
    (∃ u : ι → K, ∀ e : α × Fin (s + 1),
      ∑ i, (P * V e.1 i).coeff e.2.val * u i = (B e.1).coeff e.2.val) := by
  classical
  apply exists_congr
  intro u
  constructor
  · intro hu e
    have h := Polynomial.X_pow_dvd_iff.mp (hu e.1) e.2.val e.2.isLt
    simpa only [Polynomial.coeff_sub, sub_eq_zero, weighted_poly_coeff] using h
  · intro hu a
    apply Polynomial.X_pow_dvd_iff.mpr
    intro n hn
    simpa only [Polynomial.coeff_sub, sub_eq_zero, weighted_poly_coeff]
      using hu (a, ⟨n, hn⟩)

private lemma truncated_poly_family_rank
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (s : ℕ) (P : Polynomial K) (V : α → ι → Polynomial K)
    (B : α → κ → Polynomial K) :
    (∃ k, ¬ ∃ u : ι → K, ∀ a,
      Polynomial.X ^ (s + 1) ∣ P * (∑ i, Polynomial.C (u i) * V a i) - B a k) ↔
      let Ac : Matrix (α × Fin (s + 1)) ι K := fun e i => (P * V e.1 i).coeff e.2.val
      let Bc : Matrix (α × Fin (s + 1)) κ K := fun e k => (B e.1 k).coeff e.2.val
      Ac.rank < (Matrix.fromCols Ac Bc).rank := by
  exact (exists_congr fun k => not_congr (truncated_poly_system_iff K α ι s P V (fun a => B a k))).trans
    (finite_family_rank_obstruction K (α × Fin (s + 1)) ι κ
      (fun e i => (P * V e.1 i).coeff e.2.val) (fun e k => (B e.1 k).coeff e.2.val))

private lemma inverse_mod_dvd_iff
    {R : Type*} [CommRing R] (D P Q F B : R) (hinv : D ∣ Q * P - 1) :
    D ∣ P * F - B ↔ D ∣ F - Q * B := by
  constructor
  · intro h
    have hh := dvd_sub (dvd_mul_of_dvd_right h Q) (dvd_mul_of_dvd_left hinv F)
    convert hh using 1
    ring
  · intro h
    have hh := dvd_add (dvd_mul_of_dvd_right h P) (dvd_mul_of_dvd_left hinv B)
    convert hh using 1
    ring

theorem solution
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (s : ℕ) (c : K) (V : α → ι → Polynomial K) (B : α → κ → Polynomial K) :
    let G : Polynomial K := ∑ k ∈ Finset.range (s + 1), (Polynomial.C c * Polynomial.X) ^ k
    let Ac : Matrix (α × Fin (s + 1)) ι K := fun e i =>
      ((1 - Polynomial.C c * Polynomial.X) * V e.1 i).coeff e.2.val
    let Bc : Matrix (α × Fin (s + 1)) κ K := fun e k => (B e.1 k).coeff e.2.val
    let A₀ : Matrix (α × Fin (s + 1)) ι K := fun e i => (V e.1 i).coeff e.2.val
    let B₀ : Matrix (α × Fin (s + 1)) κ K := fun e k => (G * B e.1 k).coeff e.2.val
    (Ac.rank < (Matrix.fromCols Ac Bc).rank) ↔
      A₀.rank < (Matrix.fromCols A₀ B₀).rank := by
  classical
  let P : Polynomial K := 1 - Polynomial.C c * Polynomial.X
  let G : Polynomial K := ∑ k ∈ Finset.range (s + 1), (Polynomial.C c * Polynomial.X) ^ k
  have hinv : Polynomial.X ^ (s + 1) ∣ G * P - 1 := by
    refine ⟨-(Polynomial.C c) ^ (s + 1), ?_⟩
    dsimp [G, P]
    rw [geom_sum_mul_neg, mul_pow]
    ring
  have hleft := truncated_poly_family_rank K α ι κ s P V B
  have hright := truncated_poly_family_rank K α ι κ s 1 V (fun a k => G * B a k)
  simp only [one_mul] at hright
  apply hleft.symm.trans
  apply Iff.trans ?_ hright
  apply exists_congr
  intro k
  apply not_congr
  apply exists_congr
  intro u
  apply forall_congr'
  intro a
  exact inverse_mod_dvd_iff (Polynomial.X ^ (s + 1)) P G
    (∑ i, Polynomial.C (u i) * V a i) (B a k) hinv
