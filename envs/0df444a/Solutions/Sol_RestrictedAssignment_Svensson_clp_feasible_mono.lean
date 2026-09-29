-- Prove2me | solution 1 for RestrictedAssignment.Svensson.clp_feasible_mono
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:28:16.688628+00:00
-- url     : https://prove2.me/submissions/9a7c157a-1874-4de5-8026-bb8e160ed283

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

theorem aux_cfm_configs_subset {J M : Type} [Fintype J] [Fintype M] [DecidableEq J]
    [DecidableEq M] (Γ : J → Finset M) (p : J → ℝ) (T0 T : ℝ) (hT : T0 ≤ T) (i : M) :
    configs Γ p T0 i ⊆ configs Γ p T i := by
  intro C hC
  simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
  exact ⟨hC.1, hC.2.trans hT⟩

end RestrictedAssignment.Svensson

open RestrictedAssignment.Svensson

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T0 T : ℝ) (hT : T0 ≤ T) (h : CLPFeasible Γ p T0) :
    CLPFeasible Γ p T := by
  classical
  obtain ⟨x, hx0, hx1, hx2⟩ := h
  refine ⟨fun i C => if C ∈ configs Γ p T0 i then x i C else 0, ?_, ?_, ?_⟩
  · intro i C
    dsimp only
    split_ifs
    · exact hx0 i C
    · exact le_refl 0
  · intro i
    have hsub := aux_cfm_configs_subset Γ p T0 T hT i
    calc ∑ C ∈ configs Γ p T i, (if C ∈ configs Γ p T0 i then x i C else 0)
        = ∑ C ∈ configs Γ p T0 i, (if C ∈ configs Γ p T0 i then x i C else 0) := by
          symm
          apply Finset.sum_subset hsub
          intro C _ hC
          simp [hC]
      _ = ∑ C ∈ configs Γ p T0 i, x i C := by
          apply Finset.sum_congr rfl
          intro C hC
          simp [hC]
      _ ≤ 1 := hx1 i
  · intro j
    refine (hx2 j).trans ?_
    apply Finset.sum_le_sum
    intro i _
    have hsub := aux_cfm_configs_subset Γ p T0 T hT i
    calc ∑ C ∈ (configs Γ p T0 i).filter (fun C => j ∈ C), x i C
        = ∑ C ∈ (configs Γ p T0 i).filter (fun C => j ∈ C),
            (if C ∈ configs Γ p T0 i then x i C else 0) := by
          apply Finset.sum_congr rfl
          intro C hC
          rw [Finset.mem_filter] at hC
          simp [hC.1]
      _ ≤ ∑ C ∈ (configs Γ p T i).filter (fun C => j ∈ C),
            (if C ∈ configs Γ p T0 i then x i C else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset_filter _ hsub
          · intro C _ _
            split_ifs
            · exact hx0 i C
            · exact le_refl 0
