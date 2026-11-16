-- Prove2me | solution 1 for QnAudit.corrected_shell_still_short
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:55:03.340085+00:00
-- url     : https://prove2.me/submissions/d0b573d0-7fba-49e1-b43d-886920b73280

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (g gamma : ℝ)
    (hg : 10 ≤ g)
    (hs : gamma^2 < g^2+5/4) : gamma-g < 1 := by
  by_contra h
  have hd : g+1 ≤ gamma := by linarith
  have hm := mul_self_le_mul_self (by linarith : 0 ≤ g+1) hd
  nlinarith
