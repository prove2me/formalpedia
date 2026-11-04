-- Prove2me | solution 1 for PerishBaseStock.Backlog.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:25:04.963236+00:00
-- url     : https://prove2.me/submissions/dbac428d-1974-4e06-8908-5bcc0f1f1b09

import Theorems.Thm_PerishBaseStock_Backlog_lemma_5
import Theorems.Thm_PerishBaseStock_Backlog_proposition_4

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (hL : 1 ≤ c.L) (S : ℝ≥0) (hS : IsHeuristicLevel P c S) :
    bsCost P c S ≤ OPT P c + ENNReal.ofReal
      ((((c.m : ℝ) - 1) * c.θ + (c.b * ((c.m : ℝ) + c.L) + c.h + c.θ) * c.L) /
          ((c.m : ℝ) + c.L) *
        expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S) := by
  have h13 := (lemma_5 P c hc S).1
  have h4 := proposition_4 P c hc hL S hS
  have hpos : (0 : ℝ) < (c.m : ℝ) + c.L := by
    have : (1 : ℝ) ≤ c.m := by exact_mod_cast hc.1
    positivity
  have key : c.h * expectedHolding (leadTimeLaw P c.L) S +
          c.b * expectedShortfall (leadTimeLaw P c.L) S +
          (c.θ + c.b * c.L) * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S =
      heuristicCost P c S +
      (((c.m : ℝ) - 1) * c.θ + (c.b * ((c.m : ℝ) + c.L) + c.h + c.θ) * c.L) /
          ((c.m : ℝ) + c.L) *
        expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S := by
    unfold heuristicCost
    field_simp
    ring
  rw [key] at h13
  calc bsCost P c S ≤ _ := h13
    _ ≤ _ := ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr
