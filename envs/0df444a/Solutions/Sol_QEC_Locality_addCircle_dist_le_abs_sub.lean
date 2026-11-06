-- Prove2me | solution 1 for QEC.Locality.addCircle_dist_le_abs_sub
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:19:11.850243+00:00
-- url     : https://prove2.me/submissions/1ab276d7-fb45-4f84-8348-78d3a2f48126

import Mathlib.Analysis.Normed.Group.AddCircle

set_option autoImplicit false
open Metric
noncomputable section

theorem solution (w a x : ℝ) (hw : 0 < w) :
    dist (a : AddCircle w) (x : AddCircle w) ≤ |x - a| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  simpa only [Real.norm_eq_abs, abs_sub_comm] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples w) (m := a - x))
