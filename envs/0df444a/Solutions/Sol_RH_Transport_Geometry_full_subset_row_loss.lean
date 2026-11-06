-- Prove2me | solution 1 for RH.Transport.Geometry.full_subset_row_loss
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:07.002862+00:00
-- url     : https://prove2.me/submissions/147d73e7-77d8-4d4e-a10e-ae7e8d1ecf22

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : 0 < p) :
    max 0 (5 * ell p - 1 + ell p) / 4 = 3 * p / 2 := by
  have hn : 0 ≤ 5 * ell p - 1 + ell p := by
    dsimp [ell]
    linarith
  rw [max_eq_right hn]
  dsimp [ell]
  ring
