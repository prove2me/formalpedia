-- Prove2me | solution 1 for RH.Transport.Geometry.boundary_gt_thirteen_fifteenths
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:47.942313+00:00
-- url     : https://prove2.me/submissions/d8bfdbc9-a8cc-4eea-842f-e45fe1b1f286

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ}
    (hp : p < 1 / 30) : (13 / 15 : ℝ) < boundary p := by
  unfold boundary
  linarith
