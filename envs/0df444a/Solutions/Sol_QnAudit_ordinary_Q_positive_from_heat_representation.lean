-- Prove2me | solution 1 for QnAudit.ordinary_Q_positive_from_heat_representation
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:14:34.11052+00:00
-- url     : https://prove2.me/submissions/fadaca9b-58ab-40ad-b315-762e633da2dd

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_oldQ_pos
open MeasureTheory Set
open QnAudit

theorem solution
    (Q : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hrep : ∀ n ≥ 1, ∀ u > 0, Q n u = oldQ K u n)
    (hK : ∀ t > 0, 0 < K t)
    (hint : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    ∀ n ≥ 1, ∀ u > 0, 0 < Q n u := by
  intro n hn u hu
  rw [hrep n hn u hu]
  exact oldQ_pos K u n hu hK (hint n hn u hu)
