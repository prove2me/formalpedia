-- Prove2me | solution 1 for Supermodularity.Matching.argmax_increasing_and_matching_exists_of_loose
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:51:37.269226+00:00
-- url     : https://prove2.me/submissions/17d6d664-c8ae-462c-96be-37ba0966aa99

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching

namespace Supermodularity.Matching

theorem aux_amlo_part1
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    ⦃j k : Fin m⦄ (hjk : j ≤ k) :
        Supermodularity.Lattices.InducedSetOrder
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y j ≤ f x j}
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y k ≤ f x k} := by
  intro a ha b hb
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  have h := hf (Set.mem_univ (a, j)) (Set.mem_univ (b, k))
  have e1 : ((a, j) ⊔ (b, k) : (∀ i, X i) × Fin m) = (a ⊔ b, k) := by
    rw [Prod.mk_sup_mk, sup_of_le_right hjk]
  have e2 : ((a, j) ⊓ (b, k) : (∀ i, X i) × Fin m) = (a ⊓ b, j) := by
    rw [Prod.mk_inf_mk, inf_of_le_left hjk]
  rw [e1, e2] at h
  dsimp only at h
  have h1 := ha (a ⊓ b)
  have h2 := hb (a ⊔ b)
  constructor
  · intro y; linarith [ha y]
  · intro y; linarith [hb y]

end Supermodularity.Matching

open Supermodularity.Matching

theorem solution
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (hloose : ∀ x : Fin m → ∀ i, X i,
        IsOptimalMatching f x ↔ ∀ j : Fin m, ∀ y : ∀ i, X i, f y j ≤ f (x j) j) :
    (∀ ⦃j k : Fin m⦄, j ≤ k →
        Supermodularity.Lattices.InducedSetOrder
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y j ≤ f x j}
          {x : ∀ i, X i | ∀ y : ∀ i, X i, f y k ≤ f x k}) ∧
      ∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x := by
  refine ⟨fun j k hjk => aux_amlo_part1 f hf hjk, ?_⟩
  classical
  have hne : ∀ j : Fin m,
      (Finset.univ.filter (fun x : ∀ i, X i => ∀ y, f y j ≤ f x j)).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := Finite.exists_max (fun x : ∀ i, X i => f x j)
    exact ⟨x, by simp [hx]⟩
  let x : Fin m → ∀ i, X i := fun j =>
    (Finset.univ.filter (fun x : ∀ i, X i => ∀ y, f y j ≤ f x j)).sup' (hne j) id
  have hmem : ∀ j, x j ∈ {x : ∀ i, X i | ∀ y : ∀ i, X i, f y j ≤ f x j} := by
    intro j
    apply Finset.sup'_mem
    · intro a ha b hb
      exact (aux_amlo_part1 f hf (le_refl j) ha hb).2
    · intro i hi
      simpa using hi
  have hge : ∀ j (z : ∀ i, X i), (∀ y, f y j ≤ f z j) → z ≤ x j := by
    intro j z hz
    exact Finset.le_sup' id (by simpa using hz)
  refine ⟨x, ?_, ?_⟩
  · intro j k hjk
    have h1 := (aux_amlo_part1 f hf hjk (hmem j) (hmem k)).2
    have h2 := hge k _ h1
    exact le_sup_left.trans h2
  · rw [hloose]
    intro j
    exact hmem j
