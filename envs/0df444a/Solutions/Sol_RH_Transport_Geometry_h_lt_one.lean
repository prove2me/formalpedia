-- Prove2me | solution 1 for RH.Transport.Geometry.h_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:04:20.761193+00:00
-- url     : https://prove2.me/submissions/4307b720-aea4-4b16-9bc9-c9db8d66b640

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : p < 1 / 30) : h p < 1 := by
  dsimp [h]
  linarith
