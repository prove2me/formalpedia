-- Prove2me | solution 1 for RhinViola.reciprocalGapTailHasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:33:30.797249+00:00
-- url     : https://prove2.me/submissions/e5944387-d0fb-45bf-a7db-41a23925ae4a

import Theorems.Thm_RhinViola_reciprocalTailDifferenceHasSum
import Mathlib.Tactic

theorem solution (h d : ℕ) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (((k + h + 1 : ℕ) : ℝ)) -
        (1 : ℝ) / (((k + h + d + 1 : ℕ) : ℝ)))
      (Finset.sum (Finset.range d) (fun j : ℕ =>
        (1 : ℝ) / (((h + j + 1 : ℕ) : ℝ)))) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hstep :=
        RhinViola.reciprocalTailDifferenceHasSum (h + d)
      have hadd := ih.add hstep
      convert hadd using 1
      · funext k
        push_cast
        ring
      · rw [Finset.sum_range_succ]
