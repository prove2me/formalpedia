-- Prove2me | solution 1 for RH.Transport.Geometry.supply_gt_inverse_capacity
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:26.294839+00:00
-- url     : https://prove2.me/submissions/cee253d7-06f3-4e49-86c1-c36e07da4674

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : 0 < p) :
    (7 / 37 : ℝ) < ell p / h p := by
  have hpos : 0 < h p := by
    unfold h
    linarith
  rw [lt_div_iff₀ hpos]
  unfold ell h
  ring_nf
  linarith
