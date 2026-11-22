-- Prove2me | solution 1 for ProConChoice.Rational.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:22:33.13443+00:00
-- url     : https://prove2.me/submissions/8f82cc1b-1019-4cf8-afd5-e884b2c9cfd0

import Mathlib
import Definitions.Def_ProConChoice_Rational_RandomChoice

set_option autoImplicit false

open ProConChoice.Rational

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → Finset X → ℝ) (hp : IsRCF p) (S : Finset X) (hS : S.Nonempty) :
    ∑ a : X, |mobiusQ p a S| ≤ (2 : ℝ) ^ (Fintype.card X - S.card) := by
  have h1 : ∀ a : X, |mobiusQ p a S| ≤
      ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => insert a S ⊆ T), p a T := by
    intro a
    unfold mobiusQ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl ?_))
    intro T hT
    rw [Finset.mem_filter] at hT
    have haT : a ∈ T := hT.2 (Finset.mem_insert_self a S)
    have hT0 : 0 ≤ p a T := (hp T ⟨a, haT⟩).1 a haT
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hT0]
  have h2 : ∑ a : X,
      ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => insert a S ⊆ T), p a T
      = ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T), ∑ a ∈ T, p a T := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hST : S ⊆ T
    · simp [Finset.insert_subset_iff, hST]
    · simp [Finset.insert_subset_iff, hST]
  have h3 : ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T), ∑ a ∈ T, p a T
      = ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T), (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mem_filter] at hT
    exact (hp T (hS.mono hT.2)).2
  have hIcc : (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T) = Finset.Icc S Finset.univ := by
    ext T
    simp [Finset.mem_Icc]
  calc ∑ a : X, |mobiusQ p a S|
      ≤ ∑ a : X, ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => insert a S ⊆ T), p a T :=
        Finset.sum_le_sum (fun a _ => h1 a)
    _ = ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T), (1 : ℝ) := by rw [h2, h3]
    _ = (2 : ℝ) ^ (Fintype.card X - S.card) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, hIcc,
          Finset.card_Icc_finset (Finset.subset_univ S), Finset.card_univ]
        push_cast
        ring
