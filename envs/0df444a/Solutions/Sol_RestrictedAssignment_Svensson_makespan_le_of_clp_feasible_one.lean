-- Prove2me | solution 1 for RestrictedAssignment.Svensson.makespan_le_of_clp_feasible_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T04:59:53.230097+00:00
-- url     : https://prove2.me/submissions/056471a2-1c9c-473a-bb5c-edcc80ad9ef1

import Mathlib.Tactic
import Mathlib.Order.WellFounded
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule
import Theorems.Thm_RestrictedAssignment_Svensson_valid_of_reachable
import Theorems.Thm_RestrictedAssignment_Svensson_exists_potential_move
import Theorems.Thm_RestrictedAssignment_Svensson_extendSchedule_terminates

open Finset Classical
open RestrictedAssignment.Svensson

namespace SchedulingAssembly

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]

omit [Fintype M] in
lemma step_preserves_assigned (Γ : J → Finset M) (p : J → ℝ) (jnew : J)
    (s s' : AlgState J M) (hstep : Step Γ p jnew s s') (j : J) (hj : s.σ j ≠ none) :
    s'.σ j ≠ none := by
  obtain ⟨_, a, i, _, _, k, hk, _, rfl⟩ := hstep
  split_ifs
  · by_cases h : j = a
    · subst j; simp
    · simpa [Function.update_of_ne h] using hj
  · exact hj
  · exact hj
  · exact hj

omit [Fintype M] in
lemma reachable_preserves_assigned (Γ : J → Finset M) (p : J → ℝ)
    (σ0 : J → Option M) (jnew : J) (s : AlgState J M)
    (hs : Reachable Γ p σ0 jnew s) (j : J) (hj : σ0 j ≠ none) : s.σ j ≠ none := by
  induction hs with
  | refl => exact hj
  | tail _ hstep ih => exact step_preserves_assigned Γ p jnew _ _ hstep j ih

lemma step_exists (Γ : J → Finset M) (p : J → ℝ) (jnew : J) (s : AlgState J M)
    (hloop : s.σ jnew = none) (hex : ∃ j i, IsPotentialMove Γ p s j i) :
    ∃ s', Step Γ p jnew s s' := by
  let P : Finset (J × M) := univ.filter (fun ji ↦ IsPotentialMove Γ p s ji.1 ji.2)
  have hP : P.Nonempty := by
    obtain ⟨j, i, h⟩ := hex
    exact ⟨(j, i), by simp [P, h]⟩
  obtain ⟨⟨j, i⟩, hji, hmin⟩ := Finset.exists_min_image P (fun ji ↦ moveVal Γ p s ji.1 ji.2) hP
  have hpm : IsPotentialMove Γ p s j i := (Finset.mem_filter.mp hji).2
  have hJT : InJT s j := by
    obtain ⟨t, ht⟩ := hpm
    cases t <;> exact ht.1
  obtain ⟨B, hB, hjB⟩ := hJT
  obtain ⟨⟨k, hk⟩, hBk⟩ := List.mem_iff_get.mp hB
  refine ⟨_, hloop, j, i, hpm, ?_, k, hk, ?_, rfl⟩
  · intro j' i' h'
    exact hmin (j', i') (by simp [P, h'])
  · exact hBk.symm ▸ hjB

lemma extend_one_positive (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hLP : CLPFeasible Γ p 1) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) :
    ∃ σ : J → Option M, Valid Γ p σ ∧ σ jnew ≠ none ∧
      ∀ j, σ0 j ≠ none → σ j ≠ none := by
  have hacc : Acc (fun s' s ↦ Step Γ p jnew s s') (initState σ0 jnew) := by
    by_contra h
    exact extendSchedule_terminates Γ p hp σ0 jnew hσ0 hjnew
      (not_acc_iff_exists_descending_chain.mp h)
  have hfinish : ∀ s, Acc (fun s' s ↦ Step Γ p jnew s s') s →
      Reachable Γ p σ0 jnew s →
      ∃ t, Reachable Γ p σ0 jnew t ∧ t.σ jnew ≠ none := by
    intro s ha
    induction ha with
    | intro s _ ih =>
      intro hs
      by_cases hloop : s.σ jnew = none
      · obtain ⟨t, ht⟩ := step_exists Γ p jnew s hloop
          (exists_potential_move Γ p (fun j ↦ (hp j).le) hLP σ0 jnew hσ0 hjnew s hs hloop)
        exact ih t ht (hs.tail ht)
      · exact ⟨s, hs, hloop⟩
  obtain ⟨t, ht, hjt⟩ := hfinish _ hacc (Relation.ReflTransGen.refl)
  exact ⟨t.σ, valid_of_reachable Γ p σ0 jnew hσ0 hjnew t ht, hjt,
    fun j hj ↦ reachable_preserves_assigned Γ p σ0 jnew t ht j hj⟩

lemma total_schedule_positive (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hLP : CLPFeasible Γ p 1) :
    ∃ σ : J → M, (∀ j, σ j ∈ Γ j) ∧ ∀ i, schedLoad p σ i ≤ 1 + 16 / 17 := by
  let P : Finset (J → Option M) := univ.filter (Valid Γ p)
  have hP : P.Nonempty := by
    refine ⟨fun _ ↦ none, ?_⟩
    simp only [P, mem_filter, mem_univ, true_and]
    constructor
    · simp
    · intro i
      have hnone : (none : Option M) ≠ some i := by intro h; cases h
      norm_num [pload, R, hnone]
  obtain ⟨σ, hσ, hmin⟩ := Finset.exists_min_image P
    (fun σ ↦ (univ.filter (fun j ↦ σ j = none)).card) hP
  have hv : Valid Γ p σ := (mem_filter.mp hσ).2
  have hall : ∀ j, σ j ≠ none := by
    intro j hj
    obtain ⟨σ', hv', hj', hpres⟩ := extend_one_positive Γ p hp hLP σ j hv hj
    have hsub : univ.filter (fun j ↦ σ' j = none) ⊂ univ.filter (fun j ↦ σ j = none) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro k hk
        simp only [mem_filter, mem_univ, true_and] at hk ⊢
        by_contra h
        exact hpres k h hk
      · intro heq
        have : j ∈ univ.filter (fun j ↦ σ' j = none) := heq.symm ▸ (by simp [hj])
        exact hj' (by simpa using this)
    have hlt := Finset.card_lt_card hsub
    have hle := hmin σ' (by simp [P, hv'])
    omega
  let σt : J → M := fun j ↦ (σ j).get (Option.isSome_iff_ne_none.mpr (hall j))
  have hσt : ∀ j, σ j = some (σt j) := by
    intro j
    exact (Option.some_get _).symm
  refine ⟨σt, fun j ↦ hv.1 j _ (hσt j), fun i ↦ ?_⟩
  have heq : schedLoad p σt i = pload p σ i := by
    unfold schedLoad pload
    apply sum_congr
    · ext j; simp only [mem_filter, mem_univ, true_and, hσt, Option.some.injEq]
    · intro _ _; rfl
  rw [heq]
  exact (hv.2 i).2

lemma restrict_clp (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hLP : CLPFeasible Γ p 1) (A : J → Prop) [DecidablePred A] :
    CLPFeasible (fun j : Subtype A ↦ Γ j) (fun j : Subtype A ↦ p j) 1 := by
  obtain ⟨x, hx0, hx1, hx2⟩ := hLP
  let f : Finset J → Finset (Subtype A) := fun C ↦ C.subtype A
  have hmap (i : M) (C : Finset J) (hC : C ∈ configs Γ p 1 i) :
      f C ∈ configs (fun j : Subtype A ↦ Γ j) (fun j : Subtype A ↦ p j) 1 i := by
    simp only [configs, mem_filter, mem_univ, true_and] at hC ⊢
    constructor
    · intro j hj
      exact hC.1 j (by simpa [f] using hj)
    · calc ∑ j ∈ f C, p j = ∑ j ∈ C.filter A, p j := by
            exact Finset.sum_subtype_eq_sum_filter p
          _ ≤ ∑ j ∈ C, p j :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j _ _ ↦ hp j)
          _ ≤ 1 := hC.2
  let x' : M → Finset (Subtype A) → ℝ :=
    fun i D ↦ ∑ C ∈ (configs Γ p 1 i).filter (fun C ↦ f C = D), x i C
  refine ⟨x', ?_, ?_, ?_⟩
  · intro i D
    exact sum_nonneg (fun C _ ↦ hx0 i C)
  · intro i
    change (∑ D ∈ configs (fun j : Subtype A ↦ Γ j) (fun j : Subtype A ↦ p j) 1 i,
      ∑ C ∈ (configs Γ p 1 i).filter (fun C ↦ f C = D), x i C) ≤ 1
    rw [sum_fiberwise_of_maps_to (hmap i)]
    exact hx1 i
  · intro j
    have heq (i : M) :
        (∑ D ∈ (configs (fun j : Subtype A ↦ Γ j) (fun j : Subtype A ↦ p j) 1 i).filter
          (fun D ↦ j ∈ D), x' i D) =
        ∑ C ∈ (configs Γ p 1 i).filter (fun C ↦ j.val ∈ C), x i C := by
      unfold x'
      rw [sum_fiberwise_eq_sum_filter]
      apply sum_congr
      · apply filter_congr
        intro C hC
        simp [hmap i C hC, f]
      · intro _ _; rfl
    simp_rw [heq]
    exact hx2 j

lemma allowed_nonempty (Γ : J → Finset M) (p : J → ℝ) (hLP : CLPFeasible Γ p 1)
    (j : J) : (Γ j).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  obtain ⟨x, _, _, hx⟩ := hLP
  have hzero : (∑ i, ∑ C ∈ (configs Γ p 1 i).filter (fun C ↦ j ∈ C), x i C) = 0 := by
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro C hC
    exfalso
    obtain ⟨hC, hj⟩ := mem_filter.mp hC
    have ha := (mem_filter.mp hC).2.1 j hj
    simp [h] at ha
  have := hx j
  linarith

end SchedulingAssembly

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hLP : CLPFeasible Γ p 1) :
    ∃ σ : J → M, (∀ j, σ j ∈ Γ j) ∧ ∀ i, schedLoad p σ i ≤ 1 + 16 / 17 := by
  classical
  let A : J → Prop := fun j ↦ 0 < p j
  obtain ⟨σp, hσp, hload⟩ := SchedulingAssembly.total_schedule_positive
    (fun j : Subtype A ↦ Γ j) (fun j : Subtype A ↦ p j) (fun j ↦ j.property)
    (SchedulingAssembly.restrict_clp Γ p hp hLP A)
  let σ : J → M := fun j ↦ if hj : A j then σp ⟨j, hj⟩
    else (SchedulingAssembly.allowed_nonempty Γ p hLP j).choose
  refine ⟨σ, ?_, fun i ↦ ?_⟩
  · intro j
    dsimp [σ]
    split_ifs with hj
    · exact hσp ⟨j, hj⟩
    · exact (SchedulingAssembly.allowed_nonempty Γ p hLP j).choose_spec
  · have heq : schedLoad p σ i =
        schedLoad (fun j : Subtype A ↦ p j) σp i := by
      unfold schedLoad
      simp only [sum_filter]
      have hzero (j : J) (hj : ¬ A j) : p j = 0 := by
        have hnot : ¬ 0 < p j := hj
        exact le_antisymm (le_of_not_gt hnot) (hp j)
      have hfilter : (∑ j ∈ univ.filter A, if σ j = i then p j else 0) =
          ∑ j : J, if σ j = i then p j else 0 := by
        apply sum_subset (filter_subset _ _)
        intro j _ hj
        have hA : ¬ A j := by simpa using hj
        simp [hzero j hA]
      rw [← hfilter]
      have hsub := Finset.sum_subtype_eq_sum_filter
        (s := (univ : Finset J)) (p := A) (fun j ↦ if σ j = i then p j else 0)
      rw [← hsub]
      simp only [Finset.subtype_univ]
      apply sum_congr rfl
      intro j _
      simp [σ, j.property]
    rw [heq]
    exact hload i
