-- Prove2me | solution 1 for Supermodularity.Matching.isIncreasing_of_optimal_of_jointlyStrictlySupermodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:09:52.927565+00:00
-- url     : https://prove2.me/submissions/b6e5f20c-84a3-45d3-8430-80450a7736c7

import Mathlib
import Definitions.Def_Supermodularity_Matching_StrictlySupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching

namespace Supermodularity.Matching

theorem aux_iojss_le {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ) (x : Fin m → ∀ i, X i) (h : IsOptimalMatching f x)
    (j : Fin m) (z : ∀ i, X i) : f z j ≤ f (x j) j := by
  have h1 := h (Function.update x j z)
  have key : ∑ i, f (Function.update x j z i) i - ∑ i, f (x i) i = f z j - f (x j) j := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  linarith

end Supermodularity.Matching

open Supermodularity.Matching

theorem solution
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : StrictlySupermodularOn (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    ∀ x : Fin m → ∀ i, X i, IsOptimalMatching f x → IsIncreasingMatching x := by
  intro x hx j k hjk
  by_contra hne
  rcases eq_or_lt_of_le hjk with hjk' | hlt
  · subst hjk'
    exact hne le_rfl
  have h1 : ¬ ((x j, j) : (∀ i, X i) × Fin m) ≤ (x k, k) := by
    intro hle
    exact hne (Prod.mk_le_mk.mp hle).1
  have h2 : ¬ ((x k, k) : (∀ i, X i) × Fin m) ≤ (x j, j) := by
    intro hle
    exact absurd (Prod.mk_le_mk.mp hle).2 (not_le.mpr hlt)
  have hs := hf (Set.mem_univ ((x j, j) : (∀ i, X i) × Fin m))
    (Set.mem_univ ((x k, k) : (∀ i, X i) × Fin m)) h1 h2
  simp only [Prod.fst_sup, Prod.snd_sup, Prod.fst_inf, Prod.snd_inf,
    sup_of_le_right hjk, inf_of_le_left hjk] at hs
  have a1 := aux_iojss_le f x hx k (x j ⊔ x k)
  have a2 := aux_iojss_le f x hx j (x j ⊓ x k)
  linarith
