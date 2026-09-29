-- Prove2me | solution 1 for Supermodularity.Matching.isOrdered_of_optimal_of_strictlySupermodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:31:25.101525+00:00
-- url     : https://prove2.me/submissions/ba0e8f01-093c-4a8e-8632-41168083056d

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_StrictlySupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsOrderedMatching

namespace Supermodularity.Matching

theorem aux_iooss_pointwise {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ) (x : Fin m → ∀ i, X i) (hx : IsOptimalMatching f x)
    (j : Fin m) (y : ∀ i, X i) : f y j ≤ f (x j) j := by
  have h := hx (Function.update x j y)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h
  have hs : ∑ l ∈ Finset.univ.erase j, f (Function.update x j y l) l
      = ∑ l ∈ Finset.univ.erase j, f (x l) l := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [hs, Function.update_self] at h
  linarith

theorem aux_iooss_lt {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (hfx : ∀ j : Fin m, StrictlySupermodularOn (fun x : ∀ i, X i => f x j) Set.univ)
    (x : Fin m → ∀ i, X i) (hx : IsOptimalMatching f x) (j k : Fin m) (hjk : j < k) :
    x j ≤ x k ∨ x k ≤ x j := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  set a := x j with ha
  set b := x k with hb
  -- supermodularity at (a, j) and (a ⊓ b, k)
  have hs := @hf (a, j) (Set.mem_univ _) (a ⊓ b, k) (Set.mem_univ _)
  simp only [Prod.sup_def, Prod.inf_def, sup_inf_self, inf_left_idem] at hs
  have hmax : j ⊔ k = k := sup_of_le_right hjk.le
  have hmin : j ⊓ k = j := inf_of_le_left hjk.le
  rw [hmax, hmin] at hs
  -- strict supermodularity of f(·, k) at a, b
  have hst := hfx k (Set.mem_univ a) (Set.mem_univ b) h1 h2
  simp only at hst
  have o1 : f (a ⊓ b) j ≤ f a j := aux_iooss_pointwise f x hx j (a ⊓ b)
  have o2 : f (a ⊔ b) k ≤ f b k := aux_iooss_pointwise f x hx k (a ⊔ b)
  linarith

end Supermodularity.Matching

open Supermodularity.Matching

theorem solution
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (hfx : ∀ j : Fin m, StrictlySupermodularOn (fun x : ∀ i, X i => f x j) Set.univ) :
    ∀ x : Fin m → ∀ i, X i, IsOptimalMatching f x → IsOrderedMatching x := by
  intro x hx j k
  rcases lt_trichotomy j k with h | h | h
  · exact aux_iooss_lt f hf hfx x hx j k h
  · subst h; exact Or.inl le_rfl
  · exact (aux_iooss_lt f hf hfx x hx k j h).symm
