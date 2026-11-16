-- Prove2me | solution 1 for QnAudit.moment_pos
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:02:06.833922+00:00
-- url     : https://prove2.me/submissions/d9ebb95a-aa58-4dd6-af0c-1434b7bf23cd

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_weight_pos
import Theorems.Thm_QnAudit_positive_integral_Ioi
open MeasureTheory Set
open QnAudit

theorem solution (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < moment K x n := by
  exact positive_integral_Ioi _ (fun t ht => mul_pos (weight_pos x n t ht) (hK t ht)) hi
