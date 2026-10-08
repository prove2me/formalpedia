-- Prove2me | solution 1 for ProjSchedTW.DelayingModes.exists_minimal_delaying_mode
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T15:59:15.149107+00:00
-- url     : https://prove2.me/submissions/377d56d2-aef0-413a-891f-54c4b880d2d1

/-
Every feasible schedule obeys a minimal delaying mode of each forbidden set (Neumann-Schwindt-
Zimmermann, Project Scheduling with Time Windows and Scarce Resources, Section 2.5).

Let `F` be forbidden. Some activity of `F` has positive duration (the activities of duration 0 are
the fictitious ones, which use no resource). Among the activities of `F` with positive duration let
`i` finish first, at time `t' = S_i + p_i`. All activities of `F` that start before `t'` and have
positive duration are in progress at the latest of their start times (they have not finished, as
`i` finishes first), so by resource feasibility they form, together with the zero-duration ones, a
feasible set. Hence `B0 = {j ∈ F | S_j ≥ t'}` is a delaying alternative, `i ∉ B0`, and every
`j ∈ B0` starts after `i` finishes. A minimal delaying alternative `B ⊆ B0` has the same property.
-/
import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

set_option autoImplicit false

namespace PSLib
open ProjSchedTW.DelayingModes

theorem delaying_core {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (hP : P.StandingAssumptions) (F : Finset (Fin (n + 2))) (hF : P.IsForbidden F)
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) :
    ∃ (i : Fin (n + 2)) (B : Finset (Fin (n + 2))),
      P.IsMinimalDelayingMode F i B ∧ ∀ j ∈ B, S i + P.p i ≤ S j := by
  classical
  obtain ⟨_, hSch, hres⟩ := hS
  obtain ⟨_, hp0, hpl, hpos, _, hr0, _, _, _⟩ := hP
  have hzero : ∀ j, P.p j = 0 → ∀ k, P.r j k = 0 := by
    intro j hj k
    by_cases h0 : j = 0
    · subst h0; exact (hr0 k).1
    by_cases hl : j = Fin.last (n + 1)
    · subst hl; exact (hr0 k).2
    · exact absurd hj (Nat.pos_iff_ne_zero.1 (hpos j h0 hl))
  set Fp : Finset (Fin (n + 2)) := F.filter (fun j => 0 < P.p j) with hFp
  have hne : Fp.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    obtain ⟨k, hk⟩ := hF
    have : ∑ j ∈ F, P.r j k = 0 := by
      refine Finset.sum_eq_zero (fun j hj => hzero j ?_ k)
      by_contra hpj
      have : j ∈ Fp := Finset.mem_filter.2 ⟨hj, Nat.pos_of_ne_zero hpj⟩
      rw [hcon] at this
      simp at this
    omega
  obtain ⟨i, hi, himin⟩ := Finset.exists_min_image Fp (fun j => S j + (P.p j : ℝ)) hne
  obtain ⟨hiF, hipos⟩ := Finset.mem_filter.1 hi
  set t' : ℝ := S i + (P.p i : ℝ) with ht'
  set B0 : Finset (Fin (n + 2)) := F.filter (fun j => t' ≤ S j) with hB0
  have hSi : S i < t' := by
    have : (0 : ℝ) < P.p i := by exact_mod_cast hipos
    linarith
  have hfeas : P.IsFeasibleSet (F \ B0) := by
    rintro ⟨k, hk⟩
    set A1 : Finset (Fin (n + 2)) := (F \ B0).filter (fun j => 0 < P.p j) with hA1
    have hiA1 : i ∈ A1 := by
      refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hiF, ?_⟩, hipos⟩
      intro h
      exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hSi)
    obtain ⟨j0, hj0, hj0max⟩ := Finset.exists_max_image A1 S ⟨i, hiA1⟩
    have hsum : ∑ j ∈ F \ B0, P.r j k = ∑ j ∈ A1, P.r j k := by
      rw [hA1, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      by_cases hpj : 0 < P.p j
      · simp [hpj]
      · have : P.p j = 0 := by omega
        simp [hpj, hzero j this k]
    have hτ : (0 : ℝ) ≤ S j0 := hSch.2 j0
    have hsub : A1 ⊆ P.activeSet S (S j0) := by
      intro j hj
      obtain ⟨hjD, hjpos⟩ := Finset.mem_filter.1 hj
      obtain ⟨hjF, hjB⟩ := Finset.mem_sdiff.1 hjD
      have hjFp : j ∈ Fp := Finset.mem_filter.2 ⟨hjF, hjpos⟩
      have h1 : t' ≤ S j + (P.p j : ℝ) := himin j hjFp
      have h2 : S j0 < t' := by
        obtain ⟨hj0D, _⟩ := Finset.mem_filter.1 hj0
        obtain ⟨_, hj0B⟩ := Finset.mem_sdiff.1 hj0D
        by_contra hcon
        exact hj0B (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hj0D).1, not_lt.1 hcon⟩)
      simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hj0max j hj, by linarith⟩
    have := hres 0 le_rfl k
    have hu := hres (S j0) hτ k
    have : ∑ j ∈ A1, P.r j k ≤ P.usage S k (S j0) :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have hdel : P.IsDelayingAlternative F B0 := ⟨Finset.filter_subset _ _, hfeas⟩
  obtain ⟨B, hBle, hBmin⟩ := exists_minimal_le_of_wellFoundedLT (P.IsDelayingAlternative F) B0 hdel
  refine ⟨i, B, ⟨hF, hBmin, Finset.mem_sdiff.2 ⟨hiF, ?_⟩⟩, fun j hj => ?_⟩
  · intro hiB
    have := Finset.mem_filter.1 (hBle hiB)
    exact absurd this.2 (not_le.2 hSi)
  · exact (Finset.mem_filter.1 (hBle hj)).2

end PSLib

open ProjSchedTW.DelayingModes in
theorem solution {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (hP : P.StandingAssumptions) (F : Finset (Fin (n + 2))) (hF : P.IsForbidden F)
    (S : Fin (n + 2) → ℝ) (hS : P.IsFeasible S) :
    ∃ (i : Fin (n + 2)) (B : Finset (Fin (n + 2))),
      P.IsMinimalDelayingMode F i B ∧ ∀ j ∈ B, S i + P.p i ≤ S j :=
  PSLib.delaying_core P hP F hF S hS
