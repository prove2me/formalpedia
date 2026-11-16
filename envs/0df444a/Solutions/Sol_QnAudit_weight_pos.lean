-- Prove2me | solution 1 for QnAudit.weight_pos
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:54:07.02113+00:00
-- url     : https://prove2.me/submissions/2ad1201d-0991-408a-92b0-62f2d514daa9

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (x : ℝ) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < weight x n t := by
  exact mul_pos (pow_pos ht _) (Real.exp_pos _)
