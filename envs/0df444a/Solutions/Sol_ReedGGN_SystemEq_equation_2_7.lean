-- Prove2me | solution 1 for ReedGGN.SystemEq.equation_2_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:09:56.729391+00:00
-- url     : https://prove2.me/submissions/518ffde9-7ee6-4b2f-b4f7-4eb73cc6543e

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_QueueLength

set_option autoImplicit false
open MeasureTheory ReedGGN.SystemEq

theorem solution (μ μ₀ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (P : SamplePath) (t : ℝ) (ht : 0 ≤ t) :
    (Q P t : ℝ) =
      I μ μ₀ P t + W0 μ₀ P t + M2 μ P t + AG μ P t +
        (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t)) +
        ∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i)) := by
  simp only [Q, I, W0, M2, AG, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul, Finset.card_filter]
  push_cast
  simp
  ring
