-- Prove2me | solution 1 for TSPHeuristics.Insertion.shortcut_cycleLength_filter_le_tourLength
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:37:21.4759+00:00
-- url     : https://prove2.me/submissions/8ac44e56-01a0-4df3-aee9-74672677b630

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Length of the path `x → L₀ → ⋯ → L_{m-1} → y`. -/
def aux_scf_walk {n : ℕ} (d : Fin n → Fin n → ℝ) : Fin n → List (Fin n) → Fin n → ℝ
  | x, [], y => d x y
  | x, z :: t, y => d x z + aux_scf_walk d z t y

theorem aux_scf_walk_start {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (x a y : Fin n) (L : List (Fin n)) :
    aux_scf_walk d x L y ≤ d x a + aux_scf_walk d a L y := by
  cases L with
  | nil => simpa [aux_scf_walk] using hd.triangle x a y
  | cons z t =>
    simp only [aux_scf_walk]
    have := hd.triangle x a z
    linarith

theorem aux_scf_walk_end {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (z y : Fin n) :
    ∀ (x : Fin n) (L : List (Fin n)), aux_scf_walk d x L y ≤ aux_scf_walk d x L z + d z y
  | x, [] => by simpa [aux_scf_walk] using hd.triangle x z y
  | x, w :: t => by
    simp only [aux_scf_walk]
    have := aux_scf_walk_end d hd z y w t
    linarith

theorem aux_scf_walk_sublist {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (y : Fin n) {l₁ l₂ : List (Fin n)}
    (h : l₁.Sublist l₂) : ∀ x, aux_scf_walk d x l₁ y ≤ aux_scf_walk d x l₂ y := by
  induction h with
  | slnil => intro x; exact le_rfl
  | cons a _ ih =>
    intro x
    simp only [aux_scf_walk]
    exact (ih x).trans (aux_scf_walk_start d hd x a y _)
  | cons_cons a _ ih =>
    intro x
    simp only [aux_scf_walk]
    linarith [ih a]

theorem aux_scf_zip_walk {n : ℕ} (d : Fin n → Fin n → ℝ) (y : Fin n) :
    ∀ (x : Fin n) (t : List (Fin n)),
      (List.zipWith d (x :: t) (t ++ [y])).sum = aux_scf_walk d x t y
  | x, [] => by simp [aux_scf_walk]
  | x, z :: t => by
    have := aux_scf_zip_walk d y z t
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons, aux_scf_walk] at this ⊢
    rw [this]

theorem aux_scf_cycle_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (a : Fin n) (t : List (Fin n)) :
    TSPHeuristics.Shared.cycleLength d (a :: t) = aux_scf_walk d a t a := by
  unfold TSPHeuristics.Shared.cycleLength
  rw [List.rotate_cons_succ, List.rotate_zero]
  exact aux_scf_zip_walk d a a t

theorem aux_scf_cycle_le_walk {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (a : Fin n) (M : List (Fin n)) :
    TSPHeuristics.Shared.cycleLength d M ≤ aux_scf_walk d a M a := by
  cases M with
  | nil =>
    simp [TSPHeuristics.Shared.cycleLength, aux_scf_walk, hd.nonneg]
  | cons b t =>
    rw [aux_scf_cycle_cons]
    simp only [aux_scf_walk]
    have := aux_scf_walk_end d hd a b b t
    linarith

theorem aux_scf_sublist_cycle {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (M L : List (Fin n)) (h : M.Sublist L) :
    TSPHeuristics.Shared.cycleLength d M ≤ TSPHeuristics.Shared.cycleLength d L := by
  cases L with
  | nil =>
    rw [List.sublist_nil.1 h]
  | cons a t =>
    rw [aux_scf_cycle_cons]
    cases h with
    | cons _ h' =>
      exact (aux_scf_cycle_le_walk d hd a M).trans (aux_scf_walk_sublist d hd a h' a)
    | cons_cons _ h' =>
      rw [aux_scf_cycle_cons]
      exact aux_scf_walk_sublist d hd a h' a

theorem aux_scf_rotate {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (List.ofFn τ).rotate 1 = List.ofFn (fun k => τ (finRotate n k)) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
    congr 1
    cases n with
    | zero => simp at h2
    | succ m =>
      apply Fin.ext
      simp only [List.length_ofFn] at h2
      rw [coe_finRotate]
      split_ifs with hk
      · have : k = m := by simpa [Fin.ext_iff] using hk
        subst this
        simp
      · have : k ≠ m := fun e => hk (by simp [Fin.ext_iff, e])
        show (k + 1) % (m + 1) = k + 1
        rw [Nat.mod_eq_of_lt (by omega)]

theorem aux_scf_tour_eq {n : ℕ} (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) :
    TSPHeuristics.Shared.tourLength d τ = TSPHeuristics.Shared.cycleLength d (List.ofFn τ) := by
  unfold TSPHeuristics.Shared.cycleLength TSPHeuristics.Shared.tourLength
  rw [aux_scf_rotate]
  have : List.zipWith d (List.ofFn τ) (List.ofFn (fun k => τ (finRotate n k))) =
      List.ofFn (fun k => d (τ k) (τ (finRotate n k))) := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp
  rw [this, List.sum_ofFn]

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (τ : Equiv.Perm (Fin n)) (H : Finset (Fin n)) :
    TSPHeuristics.Shared.cycleLength d ((List.ofFn τ).filter (fun i => decide (i ∈ H))) ≤ TSPHeuristics.Shared.tourLength d τ := by
  rw [aux_scf_tour_eq]
  exact aux_scf_sublist_cycle d hd _ _ List.filter_sublist
