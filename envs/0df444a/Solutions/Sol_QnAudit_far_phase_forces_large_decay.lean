-- Prove2me | solution 1 for QnAudit.far_phase_forces_large_decay
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:02:32.050903+00:00
-- url     : https://prove2.me/submissions/4125c148-bf09-4c97-ba9d-5dff4c44fe6e

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_phase_bound
open MeasureTheory Set
open QnAudit

theorem solution (eps gamma t : ℝ)
    (he : |eps| < 1/2) (hg : 0 < gamma) (ht : 0 < t)
    (hfar : 1 < |2*eps*gamma| * t) :
    1 / t^2 - 1/4 < gamma^2 - eps^2 := by
  have hb := phase_bound eps gamma he hg
  have hgt : 1 < gamma*t := by nlinarith
  have hgdiv : 1/t < gamma := (div_lt_iff₀ ht).2 hgt
  have he0 := (abs_lt.mp he).1
  have he1 := (abs_lt.mp he).2
  have he2 : eps^2 < 1/4 := by nlinarith
  have hi : 0 < 1/t := by positivity
  have hid : (1/t)^2 = 1/t^2 := by ring
  nlinarith
