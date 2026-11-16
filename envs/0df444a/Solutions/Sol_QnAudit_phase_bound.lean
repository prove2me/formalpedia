-- Prove2me | solution 1 for QnAudit.phase_bound
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:54:36.12723+00:00
-- url     : https://prove2.me/submissions/cfd79b04-f2cc-4751-87ae-252e14df4532

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (eps gamma : ℝ)
    (he : |eps| < 1/2) (hg : 0 < gamma) :
    |2*eps*gamma| < gamma := by
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hg]
  nlinarith
