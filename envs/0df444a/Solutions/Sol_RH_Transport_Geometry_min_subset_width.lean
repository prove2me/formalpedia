-- Prove2me | solution 1 for RH.Transport.Geometry.min_subset_width
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:45.052202+00:00
-- url     : https://prove2.me/submissions/ef264375-7868-4bb7-a883-16a5e6495522

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution (p : ℝ) :
    subsetWidth p (ell p) = 1 / 2 - 3 * p := by
  dsimp [subsetWidth, width, ell]
  ring
