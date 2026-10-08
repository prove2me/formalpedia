-- Prove2me | solution 1 for ProjSchedTW.ObjectiveClasses.equal_order_partition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:56:23.25283+00:00
-- url     : https://prove2.me/submissions/34c054ca-0c7b-4343-a27a-6c489fafde4b

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

open ProjSchedTW.ObjectiveClasses in
theorem eop861_resource {n : ℕ} {K : Type} (P : Project n K) (S S' : Fin (n + 2) → ℝ)
    (hS : S ∈ feasibleSet P) (hT : S' ∈ timeFeasibleSet P)
    (hO : scheduleOrder P S' = scheduleOrder P S) : S' ∈ resourceFeasibleSet P := by
  classical
  obtain ⟨⟨hS0, hSnn, _⟩, ⟨_, _, hR⟩⟩ := hS
  obtain ⟨hT0, hTnn, _⟩ := hT
  refine ⟨hT0, hTnn, ?_⟩
  intro k t ht
  set A := activeSet P S' t with hA
  by_cases hne : A.Nonempty
  · set t0 := A.sup' hne S with ht0
    have hmem : ∀ i, i ∈ A ↔ S' i ≤ t ∧ t < S' i + (P.p i : ℝ) := by
      intro i; simp [hA, activeSet]
    have hsub : A ⊆ activeSet P S t0 := by
      intro i hi
      have hi' := (hmem i).1 hi
      have hmem2 : i ∈ activeSet P S t0 ↔ S i ≤ t0 ∧ t0 < S i + (P.p i : ℝ) := by
        simp [activeSet]
      rw [hmem2]
      refine ⟨Finset.le_sup' S hi, ?_⟩
      rw [Finset.sup'_lt_iff]
      intro j hj
      have hj' := (hmem j).1 hj
      by_cases hij : i = j
      · subst hij
        have : (0:ℝ) < P.p i := by linarith [hi'.1, hi'.2]
        linarith
      · by_contra hcon
        rw [not_lt] at hcon
        have hin : (i, j) ∈ scheduleOrder P S := ⟨hij, hcon⟩
        rw [← hO] at hin
        obtain ⟨_, h2⟩ := hin
        simp only at h2
        linarith [hj'.1, hi'.2]
    have ht0nn : 0 ≤ t0 := by
      obtain ⟨j, hj⟩ := hne
      exact le_trans (hSnn j) (Finset.le_sup' S hj)
    calc usage P S' k t = ∑ i ∈ A, P.r i k := rfl
      _ ≤ ∑ i ∈ activeSet P S t0, P.r i k := Finset.sum_le_sum_of_subset hsub
      _ = usage P S k t0 := rfl
      _ ≤ P.R k := hR k t0 ht0nn
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : usage P S' k t = 0 := by
      show ∑ i ∈ A, P.r i k = 0
      rw [hne]; simp
    rw [this]; exact Nat.zero_le _

open ProjSchedTW.ObjectiveClasses in
theorem eop861_eq {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) :
    equalOrderSet P S =
      (fun O : Set (Fin (n + 2) × Fin (n + 2)) =>
        {S' | S' ∈ orderPolytope P O ∧ scheduleOrder P S' = O}) (scheduleOrder P S) := rfl

open ProjSchedTW.ObjectiveClasses in
theorem solution {n : ℕ} {K : Type} (P : Project n K) :
    (feasibleSet P = ⋃ S ∈ feasibleSet P, equalOrderSet P S) ∧
      (equalOrderSet P '' feasibleSet P).Finite ∧
      ∀ S ∈ feasibleSet P, ∀ S' ∈ feasibleSet P,
        equalOrderSet P S ≠ equalOrderSet P S' →
          Disjoint (equalOrderSet P S) (equalOrderSet P S') := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro S hS
      refine Set.mem_biUnion hS ?_
      exact ⟨⟨hS.1, fun e he => he.2⟩, rfl⟩
    · intro S' hS'
      obtain ⟨S, hS, hmem⟩ := Set.mem_iUnion₂.1 hS'
      obtain ⟨⟨hT, _⟩, hO⟩ := hmem
      exact ⟨hT, eop861_resource P S S' hS hT hO⟩
  · apply Set.Finite.subset (Set.finite_range (fun O : Set (Fin (n + 2) × Fin (n + 2)) =>
        {S' | S' ∈ orderPolytope P O ∧ scheduleOrder P S' = O}))
    rintro _ ⟨S, _, rfl⟩
    exact ⟨scheduleOrder P S, (eop861_eq P S).symm⟩
  · intro S _ S' _ hne
    rw [Set.disjoint_left]
    intro X hX hX'
    apply hne
    rw [eop861_eq P S, eop861_eq P S', ← hX.2, ← hX'.2]
