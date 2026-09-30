-- Prove2me | solution 1 for RandomGradFree.Accelerated.c_bound_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:57:59.829911+00:00
-- url     : https://prove2.me/submissions/df8c681b-9da8-46bb-a2b0-870dd58310cf

import Definitions.Def_RandomGradFree_Accelerated_psi
import Definitions.Def_RandomGradFree_Accelerated_C
import Mathlib.Tactic
open RandomGradFree.Accelerated
open scoped BigOperators

theorem solution (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1) (k : ℕ) :
    C α k ≤ (k : ℝ) := by
  classical
  by_cases hk : k=0
  · simp [C,hk]
  · have hprod (i : ℕ) : (∏ j ∈ Finset.Ico (k-i) k, (1-α j)) ≤ 1 :=
      Finset.prod_le_one (fun j hj => sub_nonneg.mpr (hα j).2) (fun j hj => by linarith [(hα j).1])
    have hs := Finset.sum_le_sum (fun i (hi : i∈Finset.Ico 1 k) => hprod i)
    rw [C,if_neg hk]
    calc
      1+(∑ i ∈ Finset.Ico 1 k, ∏ j ∈ Finset.Ico (k-i) k, (1-α j)) ≤ 1+∑ i ∈ Finset.Ico 1 k, (1 : ℝ) := by linarith
      _ = k := by simp; rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
