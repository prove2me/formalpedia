-- Prove2me | solution 1 for RH.Transport.Geometry.boundary_decrement
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:04.368203+00:00
-- url     : https://prove2.me/submissions/ea507ffd-048d-48e2-bf50-c0307eba66c4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution (p : ℝ) :
    (7 / 8 : ℝ) - boundary p = p / 4 := by
  rw [boundary]
  ring
