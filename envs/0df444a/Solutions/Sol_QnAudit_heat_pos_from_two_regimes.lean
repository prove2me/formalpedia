-- Prove2me | solution 1 for QnAudit.heat_pos_from_two_regimes
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:02:15.02858+00:00
-- url     : https://prove2.me/submissions/14c23bc2-797a-4c1b-8606-d7598a017053

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_positive_head_controls_signed_tail
open MeasureTheory Set
open QnAudit

theorem solution (K H N E r : ℝ → ℝ) (t0 : ℝ)
    (hsplit : ∀ t > 0, K t = H t + N t + E t)
    (hH : ∀ t > 0, 0 < H t) (hN : ∀ t > 0, 0 ≤ N t)
    (hE : ∀ t > 0, |E t| ≤ r t * H t)
    (hsmall : ∀ t > 0, t ≤ t0 → r t < 1)
    (hlarge : ∀ t > 0, t0 < t → r t < 1) :
    ∀ t > 0, 0 < K t := by
  intro t ht
  rw [hsplit t ht]
  apply positive_head_controls_signed_tail _ _ _ _ (hH t ht) (hN t ht)
  · by_cases h : t ≤ t0
    · exact hsmall t ht h
    · exact hlarge t ht (lt_of_not_ge h)
  · exact hE t ht
