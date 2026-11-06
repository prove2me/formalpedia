-- Prove2me | solution 1 for RH.Transport.Geometry.ly_residual_gt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:43.186537+00:00
-- url     : https://prove2.me/submissions/a3673d2e-b5d4-4d85-af97-a33cd2f50dcb

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
    (21 / 80 : ℝ) < ly p - d := by
  simp only [ly, ell] at hd ⊢
  linarith
