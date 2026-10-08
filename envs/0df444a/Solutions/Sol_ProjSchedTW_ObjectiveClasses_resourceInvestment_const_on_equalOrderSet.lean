-- Prove2me | solution 1 for ProjSchedTW.ObjectiveClasses.resourceInvestment_const_on_equalOrderSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:42:01.679987+00:00
-- url     : https://prove2.me/submissions/8cb5feec-2b76-487f-883f-3c4c64df80f2

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

set_option autoImplicit false

namespace P8599a118

open ProjSchedTW.ObjectiveClasses

theorem mem_active {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (t : ℝ)
    (i : Fin (n + 2)) : i ∈ activeSet P S t ↔ S i ≤ t ∧ t < S i + (P.p i : ℝ) := by
  simp [activeSet]

theorem bdd {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (k : K) :
    BddAbove {u | ∃ t : ℝ, 0 ≤ t ∧ usage P S k t = u} := by
  refine ⟨∑ i, P.r i k, ?_⟩
  rintro u ⟨t, -, rfl⟩
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem usage_le_peak {n : ℕ} {K : Type} (P : Project n K) (S1 S2 : Fin (n + 2) → ℝ)
    (h : ∀ i j, i ≠ j → S2 i + (P.p i : ℝ) ≤ S2 j → S1 i + (P.p i : ℝ) ≤ S1 j)
    (h2 : ∀ i, 0 ≤ S2 i) (k : K) (t : ℝ) : usage P S1 k t ≤ peakUsage P S2 k := by
  by_cases hA : (activeSet P S1 t).Nonempty
  · obtain ⟨j, hjA, hj⟩ := Finset.exists_max_image (activeSet P S1 t) S2 hA
    have hsub : activeSet P S1 t ⊆ activeSet P S2 (S2 j) := by
      intro i hi
      have hi' := (mem_active P S1 t i).1 hi
      have hjA' := (mem_active P S1 t j).1 hjA
      rw [mem_active]
      refine ⟨hj i hi, ?_⟩
      by_contra hc0
      have hc := not_lt.mp hc0
      by_cases hij : i = j
      · subst hij
        linarith [hi'.1, hi'.2]
      · have := h i j hij hc
        linarith [hjA'.1, hi'.2]
    calc usage P S1 k t ≤ usage P S2 k (S2 j) := Finset.sum_le_sum_of_subset hsub
      _ ≤ peakUsage P S2 k := by unfold peakUsage; exact le_csSup (bdd P S2 k) ⟨S2 j, h2 j, rfl⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    simp [usage, hA]

theorem peak_le {n : ℕ} {K : Type} (P : Project n K) (S1 S2 : Fin (n + 2) → ℝ)
    (h : ∀ i j, i ≠ j → S2 i + (P.p i : ℝ) ≤ S2 j → S1 i + (P.p i : ℝ) ≤ S1 j)
    (h2 : ∀ i, 0 ≤ S2 i) (k : K) : peakUsage P S1 k ≤ peakUsage P S2 k := by
  unfold peakUsage
  refine csSup_le ⟨usage P S1 k 0, 0, le_refl 0, rfl⟩ ?_
  rintro u ⟨t, -, rfl⟩
  exact usage_le_peak P S1 S2 h h2 k t

end P8599a118

open ProjSchedTW.ObjectiveClasses in
theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    ∀ S' ∈ equalOrderSet P S, ∀ S'' ∈ equalOrderSet P S,
      resourceInvestment P c S' = resourceInvestment P c S'' := by
  intro S' hS' S'' hS''
  obtain ⟨⟨⟨_, h0', _⟩, _⟩, hO'⟩ := hS'
  obtain ⟨⟨⟨_, h0'', _⟩, _⟩, hO''⟩ := hS''
  have hO : scheduleOrder P S' = scheduleOrder P S'' := hO'.trans hO''.symm
  have hA : ∀ i j, i ≠ j → S'' i + (P.p i : ℝ) ≤ S'' j → S' i + (P.p i : ℝ) ≤ S' j := by
    intro i j hij hle
    have hm : (i, j) ∈ scheduleOrder P S'' := ⟨hij, hle⟩
    rw [← hO] at hm
    exact hm.2
  have hB : ∀ i j, i ≠ j → S' i + (P.p i : ℝ) ≤ S' j → S'' i + (P.p i : ℝ) ≤ S'' j := by
    intro i j hij hle
    have hm : (i, j) ∈ scheduleOrder P S' := ⟨hij, hle⟩
    rw [hO] at hm
    exact hm.2
  unfold resourceInvestment
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [le_antisymm (P8599a118.peak_le P S' S'' hA h0'' k) (P8599a118.peak_le P S'' S' hB h0' k)]
