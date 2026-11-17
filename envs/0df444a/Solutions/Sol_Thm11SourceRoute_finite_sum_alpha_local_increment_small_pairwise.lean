-- Prove2me | solution 1 for Thm11SourceRoute.finite_sum_alpha_local_increment_small_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:54:43.707677+00:00
-- url     : https://prove2.me/submissions/24601539-513a-4c8f-9603-0d3aa6b7f2f5

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F003
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
import Theorems.Thm_Thm11SourceRoute_finite_sum_alpha_local_increment_small
import Theorems.Thm_Thm11SourceRoute_pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset BigOperators
open Set Topology

noncomputable section

section Thm11SourceRoute
open Thm11SourceRoute


theorem solution
    {α : ℝ → ℝ}
    (S : Finset ℝ)
    (hα_mono : Monotone α)
    (hα : ∀ c : ℝ, c ∈ S → ContinuousAt α c)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ → ℝ,
      (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
      (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps ∧
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by
  classical
  rcases finite_sum_alpha_local_increment_small S hα heps with
    ⟨rho0, hrho0_pos, hsum0_lt⟩
  let cap : ℝ :=
    if (S : Set ℝ).Nontrivial then (S : Set ℝ).infsep / 4 else 1
  have hcap_pos :
      0 < cap := by
    dsimp [cap]
    by_cases hnontrivial : (S : Set ℝ).Nontrivial
    · rw [if_pos hnontrivial]
      have hinf_pos : 0 < (S : Set ℝ).infsep := by
        exact (Finset.infsep_pos_iff_nontrivial S).2 hnontrivial
      linarith
    · rw [if_neg hnontrivial]
      norm_num
  let rho : ℝ → ℝ := fun c =>
    if c ∈ S then min (rho0 c) cap else 1
  refine ⟨rho, ?_, ?_, ?_⟩
  · intro c hc
    dsimp [rho]
    rw [if_pos hc]
    exact lt_min (hrho0_pos c hc) hcap_pos
  · have hterm_le :
        ∀ c : ℝ, c ∈ S →
          α (c + rho c) - α (c - rho c) ≤
            α (c + rho0 c) - α (c - rho0 c) := by
      intro c hc
      dsimp [rho]
      rw [if_pos hc]
      exact alpha_local_increment_mono_of_radius_le hα_mono
        (min_le_left (rho0 c) cap)
    have hsum_le :
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) ≤
          ∑ c ∈ S, (α (c + rho0 c) - α (c - rho0 c)) := by
      refine Finset.sum_le_sum ?_
      intro c hc
      exact hterm_le c hc
    exact lt_of_le_of_lt hsum_le hsum0_lt
  · refine pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four S rho ?_
    intro c hc hnontrivial
    dsimp [rho]
    rw [if_pos hc]
    dsimp [cap]
    rw [if_pos hnontrivial]
    exact min_le_right (rho0 c) ((S : Set ℝ).infsep / 4)
end Thm11SourceRoute
