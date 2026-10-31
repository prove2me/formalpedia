-- Prove2me | solution 1 for PriorityAlloc.DAFlex.proposition_H_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:23:16.81471+00:00
-- url     : https://prove2.me/submissions/fb97a1c3-b703-4eb0-b255-3652a02aabea

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model
import Theorems.Thm_PriorityAlloc_DAFlex_daop_monotone_cutoff_exists
import Theorems.Thm_PriorityAlloc_DAFlex_h1_budget_at_one
import Theorems.Thm_PriorityAlloc_DAFlex_eq_H_2
import Theorems.Thm_PriorityAlloc_DAFlex_h1_cutoff_respects_quota
import Theorems.Thm_PriorityAlloc_DAFlex_eq_H_4

open PriorityAlloc.DAFlex MeasureTheory Classical

theorem solution {m n : ℕ} (M : Market m n) (hM : M.Standing) (hreg : Regular M)
    (y : Fin m → Finset (Option (Fin n)) → ℝ) (hy : Ymem M y) :
    ∃ z, IsDACutoff M (h1Law y) (lhs11 M y) 2 z ∧ ∀ t S, bsProb (h1Law y) z t S = y t S := by
  have hG := (h1_budget_at_one M y hy).1
  obtain ⟨-, -, z, hz⟩ := daop_monotone_cutoff_exists M hM (h1Law y) hG (lhs11 M y) 2
    (by norm_num)
  have h2 := eq_H_2 M hM y hy
  have h1box : (1 : Fin n → ℝ) ∈ box 2 := by
    simp only [box, Set.mem_pi, Set.mem_univ, Set.mem_Icc, Pi.one_apply, forall_const]
    norm_num
  have hz1 : z ≤ 1 := hz.2 ⟨h1box, h2.2⟩
  refine ⟨z, hz, ?_⟩
  by_contra hne
  push_neg at hne
  have hlt := eq_H_4 M hM hreg y hy z hz.1.1 hz1 hne
  have hq := h1_cutoff_respects_quota M hM y hy z hz
  have : ∑ j, demand M (h1Law y) z j ≤ ∑ j, lhs11 M y j :=
    Finset.sum_le_sum fun j _ => hq j
  linarith
