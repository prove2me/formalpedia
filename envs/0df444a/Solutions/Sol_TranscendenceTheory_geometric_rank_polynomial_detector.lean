-- Prove2me | solution 1 for TranscendenceTheory.geometric_rank_polynomial_detector
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T20:56:47.723272+00:00
-- url     : https://prove2.me/submissions/d7a2bafc-e07b-4b8e-890e-08dcfc8e53c0

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
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

private lemma common_zero_polynomial
    (K : Type*) [Field K] (d : ℕ) (T : Set (Polynomial K))
    (hT : ∀ p ∈ T, p.natDegree ≤ d) :
    ∃ g : Polynomial K, g.natDegree ≤ d ∧
      ∀ c : K, (∀ p ∈ T, p.eval c = 0) ↔ g.eval c = 0 := by
  classical
  let I : Ideal (Polynomial K) := Ideal.span T
  let g := Submodule.IsPrincipal.generator I
  have hgmem : g ∈ I := Submodule.IsPrincipal.generator_mem I
  have hspan : Ideal.span {g} = I := Ideal.span_singleton_generator I
  refine ⟨g, ?_, ?_⟩
  · by_cases hex : ∃ p ∈ T, p ≠ 0
    · obtain ⟨p, hp, hp0⟩ := hex
      have hgp : g ∣ p := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
        (Ideal.subset_span hp)
      exact (Polynomial.natDegree_le_of_dvd hgp hp0).trans (hT p hp)
    · have hbot : I = ⊥ := by
        apply le_antisymm _ bot_le
        apply Ideal.span_le.mpr
        intro p hp
        have hp0 : p = 0 := by by_contra hn; exact hex ⟨p, hp, hn⟩
        simp [hp0]
      have hg0 : g = 0 := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mp hbot
      simp [hg0]
  · intro c
    let ev : Polynomial K →+* K := Polynomial.evalRingHom c
    constructor
    · intro hz
      have hker : I ≤ RingHom.ker ev := Ideal.span_le.mpr (by
        intro p hp
        exact hz p hp)
      exact hker hgmem
    · intro hg
      have hker : I ≤ RingHom.ker ev := by
        rw [← hspan]
        apply Ideal.span_le.mpr
        intro p hp
        rcases Set.mem_singleton_iff.mp hp with rfl
        exact hg
      intro p hp
      exact hker (Ideal.subset_span hp)

private lemma polynomial_rank_detector
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (d : ℕ) (A : Matrix α ι K) (B : Matrix α κ (Polynomial K))
    (hB : ∀ a k, (B a k).natDegree ≤ d) :
    ∃ g : Polynomial K, g.natDegree ≤ d ∧ ∀ c : K,
      (A.rank < (Matrix.fromCols A (fun a k => (B a k).eval c)).rank) ↔ g.eval c ≠ 0 := by
  classical
  let S := Submodule.span K (Set.range A.col)
  let W := {f : Module.Dual K (α → K) // ∀ x ∈ S, f x = 0}
  let P : W × κ → Polynomial K := fun t =>
    ∑ a, Polynomial.C (t.1.val (Pi.single a 1)) * B a t.2
  have hdeg (t : W × κ) : (P t).natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a ha
    exact (Polynomial.natDegree_C_mul_le _ _).trans (hB a t.2)
  have hvec (c : K) (k : κ) : (fun a => (B a k).eval c) =
      ∑ a, (B a k).eval c • (Pi.single a 1 : α → K) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  have heval (f : W) (c : K) (k : κ) :
      (P (f, k)).eval c = f.val (fun a => (B a k).eval c) := by
    rw [hvec, map_sum]
    simp [P, Polynomial.eval_finsetSum, map_smul, mul_comm]
  have hmem (x : α → K) : x ∈ S ↔ ∀ f : W, f.val x = 0 := by
    constructor
    · exact fun hx f => f.property x hx
    · intro hz
      by_contra hx
      obtain ⟨f, hfx, hfS⟩ := S.exists_dual_map_eq_bot_of_notMem hx inferInstance
      have hf (y : α → K) (hy : y ∈ S) : f y = 0 := by
        have h := Submodule.mem_map_of_mem (f := f) hy
        rw [hfS] at h
        exact (Submodule.mem_bot K).mp h
      exact hfx (hz ⟨f, hf⟩)
  have hzeros (c : K) : (∀ p ∈ Set.range P, p.eval c = 0) ↔
      ∀ k, (fun a => (B a k).eval c) ∈ S := by
    constructor
    · intro hz k
      apply (hmem _).mpr
      intro f
      rw [← heval f c k]
      exact hz _ ⟨(f, k), rfl⟩
    · intro hm p hp
      obtain ⟨⟨f, k⟩, rfl⟩ := hp
      rw [heval]
      exact f.property _ (hm k)
  have hsol (c : K) (k : κ) : (fun a => (B a k).eval c) ∈ S ↔
      ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = (B a k).eval c := by
    rw [Submodule.mem_span_range_iff_exists_fun K]
    apply exists_congr
    intro u
    rw [funext_iff]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, mul_comm]
  obtain ⟨g, hg, hzero⟩ := common_zero_polynomial K d (Set.range P) (by
    rintro _ ⟨t, rfl⟩
    exact hdeg t)
  refine ⟨g, hg, ?_⟩
  intro c
  have hrank : (A.rank < (Matrix.fromCols A (fun a k => (B a k).eval c)).rank) ↔
      ¬ ∀ k, (fun a => (B a k).eval c) ∈ S := by
    rw [← finite_family_rank_obstruction K α ι κ A (fun a k => (B a k).eval c)]
    simp only [hsol, not_forall]
  exact hrank.trans (not_congr ((hzeros c).symm.trans (hzero c)))

theorem solution
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (s : ℕ) (V : α → ι → Polynomial K) (B : α → κ → Polynomial K) :
    ∃ g : Polynomial K, g.natDegree ≤ s ∧ ∀ c : K,
      let A₀ : Matrix (α × Fin (s + 1)) ι K := fun e i => (V e.1 i).coeff e.2.val
      let R : Polynomial K := ∑ r ∈ Finset.range (s + 1), (Polynomial.C c * Polynomial.X) ^ r
      let B₀ : Matrix (α × Fin (s + 1)) κ K := fun e k => (R * B e.1 k).coeff e.2.val
      (A₀.rank < (Matrix.fromCols A₀ B₀).rank) ↔ g.eval c ≠ 0 := by
  classical
  let A : Matrix (α × Fin (s + 1)) ι K := fun e i => (V e.1 i).coeff e.2.val
  let E : Matrix (α × Fin (s + 1)) κ (Polynomial K) := fun e k =>
    ∑ r ∈ Finset.range (s + 1),
      Polynomial.C ((Polynomial.X ^ r * B e.1 k).coeff e.2.val) * Polynomial.X ^ r
  have hdeg (e : α × Fin (s + 1)) (k : κ) : (E e k).natDegree ≤ s := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    exact (Polynomial.natDegree_C_mul_X_pow_le _ r).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
  have heval (c : K) (e : α × Fin (s + 1)) (k : κ) :
      (E e k).eval c =
        ((∑ r ∈ Finset.range (s + 1), (Polynomial.C c * Polynomial.X) ^ r) *
          B e.1 k).coeff e.2.val := by
    dsimp [E]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Finset.sum_mul, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro r hr
    rw [show (Polynomial.C c * Polynomial.X) ^ r * B e.1 k =
        Polynomial.C (c ^ r) * (Polynomial.X ^ r * B e.1 k) by
      rw [mul_pow, Polynomial.C_pow, mul_assoc]]
    rw [Polynomial.coeff_C_mul]
    exact mul_comm _ _
  obtain ⟨g, hg, htest⟩ := polynomial_rank_detector K (α × Fin (s + 1)) ι κ s A E hdeg
  refine ⟨g, hg, ?_⟩
  intro c
  simpa only [heval] using htest c
