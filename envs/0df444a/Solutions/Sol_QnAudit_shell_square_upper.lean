-- Prove2me | solution 1 for QnAudit.shell_square_upper
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:54:55.201743+00:00
-- url     : https://prove2.me/submissions/1470fddd-2eeb-4790-9c13-47bc5154bd7d

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (a eps gamma S : ℝ)
    (he : |eps| < 1/2) (ha : a = gamma^2-eps^2) (hs : a < S+1) :
    gamma^2 < S+5/4 := by
  have he0 := (abs_lt.mp he).1
  have he1 := (abs_lt.mp he).2
  nlinarith
