-- Prove2me | solution 1 for RestrictedAssignment.Svensson.configLP_integrality_gap
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T05:02:03.036835+00:00
-- url     : https://prove2.me/submissions/9a28d114-8384-437e-9f00-451a3e31ca06

import Mathlib.Tactic
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Theorems.Thm_RestrictedAssignment_Svensson_clp_feasible_scale
import Theorems.Thm_RestrictedAssignment_Svensson_makespan_le_of_clp_feasible_one

open Finset Classical
open RestrictedAssignment.Svensson

namespace SchedulingScaling

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]

lemma job_in_configuration (Γ : J → Finset M) (p : J → ℝ) (T : ℝ)
    (hLP : CLPFeasible Γ p T) (j : J) :
    ∃ i C, C ∈ configs Γ p T i ∧ j ∈ C := by
  by_contra h
  push Not at h
  obtain ⟨x, _, _, hx⟩ := hLP
  have heq : (∑ i, ∑ C ∈ (configs Γ p T i).filter (fun C ↦ j ∈ C), x i C) = 0 := by
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro C hC
    obtain ⟨hC, hj⟩ := mem_filter.mp hC
    exact (h i C hC hj).elim
  have := hx j
  linarith

end SchedulingScaling

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (T : ℝ) (hT : 0 ≤ T)
    (hLP : CLPFeasible Γ p T) :
    ∃ σ : J → M, (∀ j, σ j ∈ Γ j) ∧ ∀ i, schedLoad p σ i ≤ 33 / 17 * T := by
  classical
  by_cases hzero : T = 0
  · subst T
    have hconf := SchedulingScaling.job_in_configuration Γ p 0 hLP
    have hallow (j : J) : (Γ j).Nonempty := by
      obtain ⟨i, C, hC, hj⟩ := hconf j
      exact ⟨i, (mem_filter.mp hC).2.1 j hj⟩
    have hpzero (j : J) : p j = 0 := by
      obtain ⟨i, C, hC, hj⟩ := hconf j
      have hsum := (mem_filter.mp hC).2.2
      have hsingle : p j ≤ ∑ k ∈ C, p k := single_le_sum (fun k _ ↦ hp k) hj
      linarith [hp j]
    refine ⟨fun j ↦ (hallow j).choose, fun j ↦ (hallow j).choose_spec, fun i ↦ ?_⟩
    simp [schedLoad, hpzero]
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
    obtain ⟨σ, hσ, hload⟩ := makespan_le_of_clp_feasible_one Γ
      (fun j ↦ p j / T) (fun j ↦ div_nonneg (hp j) hT)
      ((clp_feasible_scale Γ p T hTpos).mp hLP)
    refine ⟨σ, hσ, fun i ↦ ?_⟩
    have heq : schedLoad (fun j ↦ p j / T) σ i = schedLoad p σ i / T := by
      simp only [schedLoad, sum_div]
    have hbound : schedLoad p σ i / T ≤ 33 / 17 := by
      rw [← heq]
      convert hload i using 1
      norm_num
    exact (div_le_iff₀ hTpos).mp hbound
