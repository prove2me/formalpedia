-- Prove2me | solution 1 for SubadditiveProphet1456.Quarter.restriction_consistency
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:59:32.465796+00:00
-- url     : https://prove2.me/submissions/a3f7e394-60f7-475c-9a41-ba708c3551f5

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

theorem sp1456_thr_restrict {n m : ℕ} (i : Fin n) (B : Bundle m) (Y Z : ScoreProfile n m)
    (j : Fin m) (hj : j ∈ B) :
    threshold i (fun k => restrictScore B (Y k)) (fun k => restrictScore B (Z k)) j =
      threshold i Y Z j := by
  simp [threshold, fullMaximum, prefixMaximum, restrictScore, hj]

theorem solution
    (n m : ℕ) (μ : Fin n → PMF (Bundle m)) (i : Fin n)
    (h : ℕ) (B A : Bundle m) (hBA : B ⊆ A) :
    capHeight μ i h B = (capHeight μ i h A).map (restrictScore B) := by
  induction h generalizing i A B with
  | zero =>
    rw [sp1456_capHeight_zero, sp1456_capHeight_zero, PMF.pure_map]
    congr 1
    funext j
    simp [restrictScore]
  | succ h ih =>
    rw [sp1456_capHeight_succ, sp1456_capHeight_succ]
    by_cases hB : B = ∅
    · subst hB
      rw [if_pos rfl]
      have h0 : restrictScore (m := m) ∅ = Function.const (Score m) 0 := by
        funext b j; simp [restrictScore]
      rw [h0, PMF.map_const]
    · have hA : A ≠ ∅ := fun hA0 => hB (Finset.subset_empty.1 (hA0 ▸ hBA))
      rw [if_neg hB, if_neg hA]
      have hc : (fun k => (μ k).bind fun L => capHeight μ k h (B ∩ L)) =
          fun k => ((μ k).bind fun L => capHeight μ k h (A ∩ L)).map (restrictScore B) := by
        funext k
        rw [PMF.map_bind]
        congr 1
        funext L
        rw [ih (i := k) (B := B ∩ L) (A := A ∩ L) (Finset.inter_subset_inter_right hBA),
          ih (i := k) (B := A ∩ L) (A := A ∩ L) subset_rfl, PMF.map_comp, PMF.map_comp]
        congr 1
        funext b j
        have hj := @hBA j
        simp only [Function.comp_apply, restrictScore, Finset.mem_inter]
        split_ifs <;> first | rfl | (exfalso; tauto)
      have hd : restrictScore (m := m) B default = default := by
        funext j
        simp only [restrictScore]
        split_ifs <;> rfl
      rw [hc, ← sp1456_indep_map _ (restrictScore B) hd]
      simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      congr 1
      funext Y
      congr 1
      funext Z
      funext j
      simp only [restrictScore]
      split_ifs with hj hj'
      · rw [← sp1456_thr_restrict i B Y Z j hj]
      · exact absurd (hBA hj) hj'
      · rfl
