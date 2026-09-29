-- Prove2me | solution 1 for RestrictedAssignment.Svensson.clp_feasible_of_schedule
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:30:14.64063+00:00
-- url     : https://prove2.me/submissions/1d3eb1df-eddf-4c03-944c-bc108d49324c

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

theorem aux_cfos_mem {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (σ : J → M) (hσ : ∀ j, σ j ∈ Γ j)
    (hload : ∀ i, schedLoad p σ i ≤ T) (i : M) :
    Finset.univ.filter (fun j => σ j = i) ∈ configs Γ p T i := by
  unfold configs
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, hload i⟩
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [← hj.2]
  exact hσ j

end RestrictedAssignment.Svensson

open RestrictedAssignment.Svensson

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (σ : J → M) (hσ : ∀ j, σ j ∈ Γ j)
    (hload : ∀ i, schedLoad p σ i ≤ T) :
    CLPFeasible Γ p T := by
  refine ⟨fun i C => if C = Finset.univ.filter (fun j => σ j = i) then 1 else 0, ?_, ?_, ?_⟩
  · intro i C
    dsimp only
    split_ifs <;> norm_num
  · intro i
    dsimp only
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  · intro j
    dsimp only
    have hnn : ∀ i, 0 ≤ ∑ C ∈ (configs Γ p T i).filter (fun C => j ∈ C),
        (if C = Finset.univ.filter (fun j => σ j = i) then (1:ℝ) else 0) := by
      intro i
      apply Finset.sum_nonneg
      intro C _
      split_ifs <;> norm_num
    calc (1:ℝ) = ∑ C ∈ (configs Γ p T (σ j)).filter (fun C => j ∈ C),
          (if C = Finset.univ.filter (fun j' => σ j' = σ j) then (1:ℝ) else 0) := by
            rw [Finset.sum_ite_eq']
            rw [if_pos]
            rw [Finset.mem_filter]
            refine ⟨aux_cfos_mem Γ p T σ hσ hload (σ j), ?_⟩
            simp
      _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ C ∈ (configs Γ p T i).filter (fun C => j ∈ C),
        (if C = Finset.univ.filter (fun j => σ j = i) then (1:ℝ) else 0))
          (fun i _ => hnn i) (Finset.mem_univ (σ j))
