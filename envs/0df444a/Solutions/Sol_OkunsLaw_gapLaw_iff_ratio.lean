-- Prove2me | solution 1 for OkunsLaw.gapLaw_iff_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:50:19.108869+00:00
-- url     : https://prove2.me/submissions/a6f41e80-020f-42bf-8ef6-d257bb456c9b

import Mathlib.Tactic.Linarith
import Definitions.Def_OkunsLaw_defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OkunsLaw

theorem solution (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hYbar : 0 < Ybar t) :
    GapLaw c Y Ybar u ubar t ↔
      Y t / Ybar t - 1 = c * (ubar t - u t) := by
  have hz : Ybar t ≠ 0 := ne_of_gt hYbar
  change ((Ybar t - Y t) / Ybar t =
    c * (u t - ubar t)) ↔ _
  constructor
  · intro h
    rw [sub_div, div_self hz] at h
    nlinarith
  · intro h
    rw [sub_div, div_self hz]
    nlinarith
