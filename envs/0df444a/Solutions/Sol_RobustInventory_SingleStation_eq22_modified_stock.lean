-- Prove2me | solution 1 for RobustInventory.SingleStation.eq22_modified_stock
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:33:45.034791+00:00
-- url     : https://prove2.me/submissions/e986378f-d0f6-49c0-bccf-3965f514a166

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation

open RobustInventory.SingleStation in
theorem RI_eq22_telescope (M : Model) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (M.A i - M.Aprev i) = M.A k := by
  induction k with
  | zero => simp [Model.Aprev]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [Model.Aprev]

open RobustInventory.SingleStation in
theorem solution (M : Model) (u : ℕ → ℝ) (k : ℕ) :
    M.stock M.wmod u k = M.xbar u k - (M.p - M.h) / (M.p + M.h) * M.A k := by
  have ht := RI_eq22_telescope M k
  have hs : ∑ i ∈ Finset.range (k + 1), (u i - M.wmod i)
      = ∑ i ∈ Finset.range (k + 1), (u i - M.wbar i)
        - (M.p - M.h) / (M.p + M.h) * ∑ i ∈ Finset.range (k + 1), (M.A i - M.Aprev i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Model.wmod]
    ring
  simp only [Model.xbar, Model.stock]
  rw [hs, ht]
  ring
