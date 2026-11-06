-- Prove2me | solution 1 for RH.Transport.Geometry.ell_lt_one_fifth
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:57:08.396219+00:00
-- url     : https://prove2.me/submissions/18c068e2-c6fe-4d9f-9db5-115c299b9fe9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : p < 1 / 30) :
    ell p < 1 / 5 := by
  unfold ell
  linarith
