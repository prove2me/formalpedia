-- Prove2me | solution 1 for SimpleGraph.exists_perm_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:19.826693+00:00
-- url     : https://prove2.me/submissions/68872815-8be9-4c36-a165-535a7aceb4ee

module
public import Definitions.Def_Euler_Orientation
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Set.Card
public import Definitions.Def_Euler_Petersen
public import Theorems.Thm_SimpleGraph_exists_perm_subset

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution : ∀ (k : ℕ) (D : Finset (V × V)),
    (∀ v, (D.filter fun p => p.1 = v).card = k) → (∀ v, (D.filter fun p => p.2 = v).card = k) →
    ∃ σ : Fin k → Equiv.Perm V, (∀ i v, (v, σ i v) ∈ D) ∧
      (∀ i j v, σ i v = σ j v → i = j) ∧ (∀ p ∈ D, ∃ i, σ i p.1 = p.2) := by
  intro k
  induction k with
  | zero =>
    intro D hout _
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun p hp => ?_⟩
    have := hout p.1
    rw [card_eq_zero] at this
    have hmem : p ∈ D.filter (fun q => q.1 = p.1) := mem_filter.mpr ⟨hp, rfl⟩
    rw [this] at hmem
    exact absurd hmem (notMem_empty _)
  | succ k ih =>
    intro D hout hin
    obtain ⟨σ₀, hσ₀⟩ := exists_perm_subset (Nat.succ_pos k) hout hin
    set M := univ.image fun v => (v, σ₀ v)
    set D' := D \ M
    have hM : ∀ p, p ∈ M ↔ σ₀ p.1 = p.2 := by
      intro p
      simp only [M, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨v, rfl⟩; rfl
      · intro h; exact ⟨p.1, Prod.ext rfl h⟩
    have hout' : ∀ v, (D'.filter fun p => p.1 = v).card = k := by
      intro v
      have : D'.filter (fun p => p.1 = v) = (D.filter fun p => p.1 = v).erase (v, σ₀ v) := by
        ext p
        simp only [D', mem_filter, mem_sdiff, mem_erase, hM]
        constructor
        · rintro ⟨⟨hpD, hpM⟩, rfl⟩
          exact ⟨fun h => hpM (by rw [h]), hpD, rfl⟩
        · rintro ⟨hne, hpD, rfl⟩
          exact ⟨⟨hpD, fun h => hne (Prod.ext rfl h.symm)⟩, rfl⟩
      have hm : (v, σ₀ v) ∈ D.filter (fun p => p.1 = v) := mem_filter.mpr ⟨hσ₀ v, rfl⟩
      rw [this, card_erase_of_mem hm, hout v]
      rfl
    have hin' : ∀ w, (D'.filter fun p => p.2 = w).card = k := by
      intro w
      have : D'.filter (fun p => p.2 = w) =
          (D.filter fun p => p.2 = w).erase (σ₀.symm w, w) := by
        ext p
        simp only [D', mem_filter, mem_sdiff, mem_erase, hM]
        constructor
        · rintro ⟨⟨hpD, hpM⟩, rfl⟩
          refine ⟨fun h => hpM ?_, hpD, rfl⟩
          rw [h]; simp
        · rintro ⟨hne, hpD, rfl⟩
          refine ⟨⟨hpD, fun h => hne (Prod.ext ?_ rfl)⟩, rfl⟩
          rw [← h]; simp
      have hm : (σ₀.symm w, w) ∈ D.filter (fun p => p.2 = w) :=
        mem_filter.mpr ⟨by simpa using hσ₀ (σ₀.symm w), rfl⟩
      rw [this, card_erase_of_mem hm, hin w]
      rfl
    obtain ⟨τ, hτD, hτdisj, hτcov⟩ := ih D' hout' hin'
    refine ⟨Fin.cons σ₀ τ, fun i v => ?_, fun i j v hij => ?_, fun p hp => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact hσ₀ v
      · exact (mem_sdiff.mp (hτD j v)).1
    · have hnot : ∀ j v, τ j v ≠ σ₀ v := by
        intro j v h
        exact (mem_sdiff.mp (hτD j v)).2 ((hM _).mpr h.symm)
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact absurd hij.symm (by simpa using hnot j v)
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (by simpa using hnot i v)
        | succ j => simp only [Fin.cons_succ] at hij; rw [hτdisj i j v hij]
    · by_cases hpM : p ∈ M
      · exact ⟨0, by simpa using (hM p).mp hpM⟩
      · obtain ⟨j, hj⟩ := hτcov p (mem_sdiff.mpr ⟨hp, hpM⟩)
        exact ⟨j.succ, by simpa using hj⟩
end SimpleGraph
