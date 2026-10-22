-- Prove2me | solution 1 for SPHardness.OrderPolytope.secondStage_value
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:13:08.069627+00:00
-- url     : https://prove2.me/submissions/321b78eb-0b8d-4cbc-87d9-0c46b4986906

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

set_option autoImplicit false
open SPHardness.OrderPolytope MeasureTheory

open Classical in
theorem S_ssv (P : Type) [Fintype P] [PartialOrder P]
    (ξ : P → ℝ) (hξ : ξ ∈ cube P) :
    secondStageValue P ξ = if ξ ∈ orderPolytope P then 0 else 1 := by
  classical
  by_cases hO : ξ ∈ orderPolytope P
  · rw [if_pos hO]
    have hset : {z | secondStageFeasible P ξ z} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, hy, hz0, hz1, hz⟩
        have hle : ∑ i : P, ∑ j : P, (if i ≤ j then (ξ i - ξ j) * y i j else 0) ≤ 0 := by
          refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
          split_ifs with h
          · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hO.2 i j h]) (hy i j)
          · exact le_refl _
        linarith
      · rintro rfl
        exact ⟨fun _ _ => 0, fun _ _ => le_refl _, le_refl _, zero_le_one, by simp⟩
    unfold secondStageValue
    rw [hset]
    simp
  · rw [if_neg hO]
    obtain ⟨i, j, hij, hlt⟩ : ∃ i j : P, i ≤ j ∧ ξ j < ξ i := by
      by_contra hcon
      push Not at hcon
      exact hO ⟨hξ, fun i j h => hcon i j h⟩
    have hne : 0 < ξ i - ξ j := by linarith
    have hfeas : secondStageFeasible P ξ 1 := by
      refine ⟨fun a b => if a = i ∧ b = j then 1 / (ξ i - ξ j) else 0, fun a b => ?_,
        zero_le_one, le_refl _, ?_⟩
      · show 0 ≤ (if a = i ∧ b = j then 1 / (ξ i - ξ j) else 0)
        split_ifs
        · exact (one_div_pos.2 hne).le
        · exact le_refl _
      · rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
        · simp [hij]
          field_simp
          rfl
        · intro b _ hb
          simp [hb]
        · intro hj; exact absurd (Finset.mem_univ j) hj
        · intro a _ ha
          refine Finset.sum_eq_zero (fun b _ => ?_)
          simp [ha]
        · intro hi; exact absurd (Finset.mem_univ i) hi
    have hgr : IsGreatest {z : ℝ | secondStageFeasible P ξ z} 1 := by
      refine ⟨hfeas, ?_⟩
      rintro z ⟨y, hy, hz0, hz1, hz⟩
      exact hz1
    unfold secondStageValue
    exact hgr.csSup_eq

open Classical in
theorem solution (P : Type) [Fintype P] [PartialOrder P]
    (ξ : P → ℝ) (hξ : ξ ∈ cube P) :
    secondStageValue P ξ = if ξ ∈ orderPolytope P then 0 else 1 := S_ssv P ξ hξ
