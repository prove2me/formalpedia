-- Prove2me | solution 1 for ProjSchedTW.ObjectiveClasses.resourceInvestment_lowerSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:49:07.516023+00:00
-- url     : https://prove2.me/submissions/3a480b44-cbf2-4bc6-a054-4c9c2f91bd0c

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

set_option autoImplicit false

namespace P2M0d354b0c
open ProjSchedTW.ObjectiveClasses

lemma mem_activeSet' {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (t : ℝ)
    (i : Fin (n + 2)) :
    i ∈ activeSet P S t ↔ S i ≤ t ∧ t < S i + (P.p i : ℝ) := by
  unfold activeSet
  simp

lemma usage_bdd {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (k : K) :
    BddAbove {u | ∃ t : ℝ, 0 ≤ t ∧ usage P S k t = u} := by
  refine ⟨∑ i, P.r i k, ?_⟩
  rintro u ⟨t, -, rfl⟩
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma le_peak {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (k : K) (t : ℝ)
    (ht : 0 ≤ t) : usage P S k t ≤ peakUsage P S k :=
  le_csSup (usage_bdd P S k) ⟨t, ht, rfl⟩

lemma peak_attained {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (k : K) :
    ∃ t : ℝ, 0 ≤ t ∧ usage P S k t = peakUsage P S k :=
  Nat.sSup_mem (s := {u | ∃ t : ℝ, 0 ≤ t ∧ usage P S k t = u})
    ⟨usage P S k 0, 0, le_refl _, rfl⟩ (usage_bdd P S k)

lemma peak_eventually {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (k : K) :
    ∀ᶠ S' in nhdsWithin S (orthant n), peakUsage P S k ≤ peakUsage P S' k := by
  obtain ⟨t0, ht0, hpk⟩ := peak_attained P S k
  have hopen : ∀ᶠ S' in nhds S, ∀ i j : Fin (n + 2), i ∈ activeSet P S t0 →
      j ∈ activeSet P S t0 → S' j < S' i + (P.p i : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i ∈ activeSet P S t0 ∧ j ∈ activeSet P S t0
    · have hi := (mem_activeSet' P S t0 i).1 hij.1
      have hj := (mem_activeSet' P S t0 j).1 hij.2
      have hlt : S j < S i + (P.p i : ℝ) := lt_of_le_of_lt hj.1 hi.2
      have hc1 : Continuous fun S' : Fin (n + 2) → ℝ => S' j := continuous_apply j
      have hc2 : Continuous fun S' : Fin (n + 2) → ℝ => S' i + (P.p i : ℝ) :=
        (continuous_apply i).add continuous_const
      filter_upwards [hc1.continuousAt.eventually_lt hc2.continuousAt hlt] with S' h _ _
      exact h
    · exact Filter.Eventually.of_forall (fun S' hi hj => absurd ⟨hi, hj⟩ hij)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hopen, self_mem_nhdsWithin]
    with S' h hS'
  rw [← hpk]
  rcases (activeSet P S t0).eq_empty_or_nonempty with hE | hne
  · show ∑ i ∈ activeSet P S t0, P.r i k ≤ _
    rw [hE]
    simp
  · obtain ⟨j0, hj0⟩ := id hne
    have ht'0 : 0 ≤ (activeSet P S t0).sup' hne S' :=
      le_trans (hS' j0) (Finset.le_sup' S' hj0)
    have hsub : activeSet P S t0 ⊆ activeSet P S' ((activeSet P S t0).sup' hne S') := by
      intro i hi
      rw [mem_activeSet']
      refine ⟨Finset.le_sup' S' hi, ?_⟩
      exact (Finset.sup'_lt_iff hne).2 (fun j hj => h i j hi hj)
    calc usage P S k t0 = ∑ i ∈ activeSet P S t0, P.r i k := rfl
      _ ≤ ∑ i ∈ activeSet P S' ((activeSet P S t0).sup' hne S'), P.r i k :=
          Finset.sum_le_sum_of_subset hsub
      _ = usage P S' k ((activeSet P S t0).sup' hne S') := rfl
      _ ≤ peakUsage P S' k := le_peak P S' k _ ht'0

end P2M0d354b0c

open ProjSchedTW.ObjectiveClasses in
theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (c : K → ℝ) (hc : ∀ k, 0 ≤ c k) :
    IsLowerSemicontinuous (resourceInvestment P c) := by
  intro S _ y hy
  have hall : ∀ᶠ S' in nhdsWithin S (orthant n), ∀ k, peakUsage P S k ≤ peakUsage P S' k :=
    Filter.eventually_all.2 (fun k => P2M0d354b0c.peak_eventually P S k)
  filter_upwards [hall] with S' h
  refine lt_of_lt_of_le hy ?_
  unfold resourceInvestment
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast h k) (hc k)
