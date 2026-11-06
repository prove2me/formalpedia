-- Prove2me | solution 1 for RH.Transport.Geometry.lx_residual_gt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:19.730139+00:00
-- url     : https://prove2.me/submissions/4b193c01-c30c-4278-9d35-3e012fd54f76

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (11 / 80 : ℝ) < lx p - d := by
  dsimp [lx]
  dsimp [ell] at hd
  linarith
