-- Prove2me | solution 1 for SubadditiveProphet1456.Quarter.capping_consistency
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:55:43.071902+00:00
-- url     : https://prove2.me/submissions/bdba8459-2379-4a65-b74f-9a321f623bec

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

open SubadditiveProphet1456.Quarter

theorem sp1456_foldl_map {α β : Type} {n : ℕ} (p : Fin n → PMF α) (f : α → β)
    (l : List (Fin n)) (L : PMF (Fin n → α)) :
    (l.foldl (fun law i => law.bind fun a => (p i).map fun z => Function.update a i z) L).map
        (fun Y k => f (Y k)) =
      l.foldl (fun law i => law.bind fun a => ((p i).map f).map fun z => Function.update a i z)
        (L.map fun Y k => f (Y k)) := by
  induction l generalizing L with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    rw [PMF.map_bind, PMF.bind_map]
    congr 1
    funext a
    simp only [Function.comp_def, PMF.map_comp]
    congr 1
    funext z k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]

theorem sp1456_indep_map {α β : Type} [Inhabited α] [Inhabited β] {n : ℕ} (p : Fin n → PMF α)
    (f : α → β) (hf : f default = default) :
    (independent p).map (fun Y k => f (Y k)) = independent (fun k => (p k).map f) := by
  unfold independent
  rw [sp1456_foldl_map]
  congr 1
  rw [PMF.pure_map]
  congr 1
  funext k
  exact hf

theorem sp1456_capHeight_zero {n m : ℕ} (μ : Fin n → PMF (Bundle m)) (i : Fin n) (A : Bundle m) :
    capHeight μ i 0 A = PMF.pure 0 := by
  simp [capHeight, capExecution, PMF.pure_map]

theorem sp1456_capHeight_succ {n m : ℕ} (μ : Fin n → PMF (Bundle m)) (i : Fin n) (h : ℕ)
    (A : Bundle m) :
    capHeight μ i (h+1) A = if A = ∅ then PMF.pure 0 else
      (independent (fun k => (μ k).bind fun L => capHeight μ k h (A ∩ L))).bind fun Y =>
      (independent (fun k => (μ k).bind fun L => capHeight μ k h (A ∩ L))).map fun Z =>
        restrictScore A (fun j => 1 + threshold i Y Z j) := by
  simp only [capHeight, capExecution]
  split_ifs with hA
  · simp [PMF.pure_map]
  · set E : Fin n → PMF (Score m × ℕ) := fun k => (μ k).bind fun L =>
      (capExecution μ h k (A ∩ L)).map fun z => (z.1, z.2 + 1 + 2*m) with hE
    have hc : (fun k => (μ k).bind fun L => (capExecution μ h k (A ∩ L)).map Prod.fst) =
        fun k => (E k).map Prod.fst := by
      funext k
      rw [hE, PMF.map_bind]
      congr 1
      funext L
      rw [PMF.map_comp]
      rfl
    rw [hc, ← sp1456_indep_map E Prod.fst rfl]
    simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

theorem sp1456_full_cap {n m : ℕ} (c : ℝ≥0) (Y : ScoreProfile n m) (j : Fin m) :
    fullMaximum (fun k j => min c (Y k j)) j = min c (fullMaximum Y j) := by
  unfold fullMaximum
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => min c x)
    (fun a b hab => min_le_min_left c hab) (by simp)]
  rfl

theorem sp1456_prefix_cap {n m : ℕ} (i : Fin n) (c : ℝ≥0) (Y : ScoreProfile n m) (j : Fin m) :
    prefixMaximum i (fun k j => min c (Y k j)) j = min c (prefixMaximum i Y j) := by
  unfold prefixMaximum
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => min c x)
    (fun a b hab => min_le_min_left c hab) (by simp)]
  rfl

theorem sp1456_prefix_le {n m : ℕ} (i : Fin n) (Y : ScoreProfile n m) (j : Fin m) :
    prefixMaximum i Y j ≤ fullMaximum Y j :=
  Finset.sup_mono (Finset.filter_subset _ _)

theorem sp1456_thr_cap {n m : ℕ} (c : ℝ≥0) (i : Fin n) (Y Z : ScoreProfile n m) (j : Fin m) :
    threshold i (fun k j => min c (Y k j)) (fun k j => min c (Z k j)) j =
      min c (threshold i Y Z j) := by
  have hz := sp1456_prefix_le i Z j
  have hy := sp1456_prefix_le i Y j
  simp only [threshold, sp1456_full_cap, sp1456_prefix_cap]
  generalize fullMaximum Y j = a at *
  generalize fullMaximum Z j = b at *
  generalize prefixMaximum i Y j = d at *
  generalize prefixMaximum i Z j = e at *
  simp only [ge_iff_le, min_def]
  split_ifs <;> order

theorem sp1456_key_cap {n m : ℕ} (i : Fin n) (h : ℕ) (A : Bundle m) (Y Z : ScoreProfile n m) :
    capScore (h+1) (restrictScore A fun j => 1 + threshold i Y Z j) =
      restrictScore A fun j =>
        1 + threshold i (fun k => capScore h (Y k)) (fun k => capScore h (Z k)) j := by
  funext j
  simp only [capScore, restrictScore]
  split_ifs with hj
  · have hY : (fun k => capScore h (Y k)) = fun k j => min (h : ℝ≥0) (Y k j) := rfl
    have hZ : (fun k => capScore h (Z k)) = fun k j => min (h : ℝ≥0) (Z k j) := rfl
    rw [hY, hZ, sp1456_thr_cap]
    push_cast
    rw [add_comm (h : ℝ≥0) 1, min_add_add_left]
  · simp

theorem solution
    (n m : ℕ) (μ : Fin n → PMF (Bundle m)) (i : Fin n)
    (ℓ h : ℕ) (hℓ : h ≤ ℓ) (A : Bundle m) :
    (capHeight μ i ℓ A).map (capScore h) = capHeight μ i h A := by
  induction h generalizing ℓ i A with
  | zero =>
    have h0 : (capScore (m := m) 0) = Function.const (Score m) 0 := by
      funext b j; simp [capScore]
    rw [h0, sp1456_capHeight_zero]
    exact PMF.map_const _ _
  | succ h ih =>
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    rw [sp1456_capHeight_succ, sp1456_capHeight_succ]
    split_ifs with hA
    · rw [PMF.pure_map]
      congr 1
      funext j
      simp [capScore]
    · have hc : (fun k => (μ k).bind fun L => capHeight μ k h (A ∩ L)) =
          fun k => ((μ k).bind fun L => capHeight μ k ℓ (A ∩ L)).map (capScore h) := by
        funext k
        rw [PMF.map_bind]
        congr 1
        funext L
        rw [ih (ℓ := ℓ) (hℓ := by omega)]
      have hd : capScore (m := m) h default = default := by
        funext j
        show min (h : ℝ≥0) (default : ℝ≥0) = default
        exact min_eq_right zero_le
      rw [hc, ← sp1456_indep_map _ (capScore h) hd]
      simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      congr 1
      funext Y
      congr 1
      funext Z
      exact sp1456_key_cap i h A Y Z
