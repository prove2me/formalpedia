-- Prove2me | solution 1 for PriorityAlloc.DAFlex.theorem_1_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:25:01.217513+00:00
-- url     : https://prove2.me/submissions/68f7b422-c985-42eb-8857-776f78a14a38

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model
import Theorems.Thm_PriorityAlloc_DAFlex_h1_budget_at_one
import Theorems.Thm_PriorityAlloc_DAFlex_proposition_H_1
import Theorems.Thm_PriorityAlloc_DAFlex_proposition_H_2_a
import Theorems.Thm_PriorityAlloc_DAFlex_proposition_H_3

open PriorityAlloc.DAFlex MeasureTheory Classical

lemma lhs11_nonneg' {m n : ℕ} (M : Market m n) (hM : M.Standing)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) (j : Fin n) :
    0 ≤ lhs11 M y j :=
  Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun S _ =>
    mul_nonneg (mul_nonneg (hM.1 t).le ENNReal.toReal_nonneg) (hy.1 t S)

lemma stbBoost_bounds' {m n : ℕ} (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) (t : Fin m) (j : Fin n) : 0 ≤ stbBoost y t j ∧ stbBoost y t j + 1 ≤ 2 := by
  unfold stbBoost
  rw [Finset.sum_filter]
  constructor
  · exact Finset.sum_nonneg fun S _ => by split_ifs; exacts [hy.1 t S, le_rfl]
  · have : ∑ S, (if some j ∈ S then y t S else 0) ≤ ∑ S, y t S :=
      Finset.sum_le_sum fun S _ => by split_ifs; exacts [le_rfl, hy.1 t S]
    rw [hy.2.2.1 t] at this; linarith

theorem solution {m n : ℕ} (M : Market m n) (hM : M.Standing) (hreg : Regular M) :
    (∀ y, Ymem M y → DAImplementable M y) ∧
      (∀ y, Ymem M y → (DASTBImplementable M y ↔ NestedWithinSegment y)) := by
  constructor
  · intro y hy
    obtain ⟨z, hz, hbs⟩ := proposition_H_1 M hM hreg y hy
    have h1 := h1_budget_at_one M y hy
    exact ⟨2, h1Law y, lhs11 M y, z, by norm_num, h1.1, h1.2.1,
      fun j => ⟨lhs11_nonneg' M hM y hy j, hy.2.1 j⟩, hz, hbs⟩
  · intro y hy
    constructor
    · rintro ⟨B, b, q, z, _, _, _, _, hbs⟩
      intro t S S' h1 h2
      exact proposition_H_2_a b z t S S' (by rw [hbs]; exact h1) (by rw [hbs]; exact h2)
    · intro hnest
      obtain ⟨z, hz, hbs⟩ := proposition_H_3 M hM hreg y hy hnest
      exact ⟨2, stbBoost y, lhs11 M y, z, by norm_num, stbBoost_bounds' M y hy,
        fun j => ⟨lhs11_nonneg' M hM y hy j, hy.2.1 j⟩, hz, hbs⟩
