-- Prove2me | solution 1 for QnAudit.ordinary_Q_positive_from_head_tail
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:17:49.969205+00:00
-- url     : https://prove2.me/submissions/bef729d7-c104-4db3-b826-54f2b95889dd

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_heat_pos_from_two_regimes
import Theorems.Thm_QnAudit_ordinary_Q_positive_from_heat_representation
open MeasureTheory Set
open QnAudit

theorem solution
    (Q : ℕ → ℝ → ℝ) (K H N E r : ℝ → ℝ) (t0 : ℝ)
    (hrep : ∀ n ≥ 1, ∀ u > 0, Q n u = oldQ K u n)
    (hint : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0))
    (hsplit : ∀ t > 0, K t = H t + N t + E t)
    (hH : ∀ t > 0, 0 < H t) (hN : ∀ t > 0, 0 ≤ N t)
    (hE : ∀ t > 0, |E t| ≤ r t * H t)
    (hsmall : ∀ t > 0, t ≤ t0 → r t < 1)
    (hlarge : ∀ t > 0, t0 < t → r t < 1) :
    ∀ n ≥ 1, ∀ u > 0, 0 < Q n u := by
  exact ordinary_Q_positive_from_heat_representation Q K hrep
    (heat_pos_from_two_regimes K H N E r t0 hsplit hH hN hE hsmall hlarge) hint
