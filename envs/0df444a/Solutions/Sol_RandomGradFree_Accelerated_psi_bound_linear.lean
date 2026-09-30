-- Prove2me | solution 1 for RandomGradFree.Accelerated.psi_bound_linear
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:58:09.523993+00:00
-- url     : https://prove2.me/submissions/f4a2b2cb-e512-43b1-b8d2-3f27d462621a

import Definitions.Def_RandomGradFree_Accelerated_psi
import Definitions.Def_RandomGradFree_Accelerated_C
import Mathlib.Tactic
open RandomGradFree.Accelerated
open scoped BigOperators

theorem solution (α : ℕ → ℝ) (n : ℕ) (κ : ℝ)
    (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hακ : ∀ j, Real.sqrt κ / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) :
    psi α k ≤ (1 - Real.sqrt κ / (4 * ((n : ℝ) + 4))) ^ k := by
  unfold psi
  calc
    (∏ i ∈ Finset.range k, (1-α i)) ≤ ∏ i ∈ Finset.range k, (1-Real.sqrt κ/(4*((n:ℝ)+4))) :=
      Finset.prod_le_prod (fun i hi => sub_nonneg.mpr (hα i).2) (fun i hi => by linarith [hακ i])
    _ = _ := by simp
