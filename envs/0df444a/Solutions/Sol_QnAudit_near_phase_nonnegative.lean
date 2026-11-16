-- Prove2me | solution 1 for QnAudit.near_phase_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:54:45.908026+00:00
-- url     : https://prove2.me/submissions/75e28234-8ff7-4373-b8c4-a0e694e37109

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (a b t : ℝ)
    (hphase : |b*t| ≤ Real.pi/2) :
    0 ≤ Real.exp (-a*t) * Real.cos (b*t) := by
  exact mul_nonneg (le_of_lt (Real.exp_pos _))
    (Real.cos_nonneg_of_mem_Icc (abs_le.mp hphase))
