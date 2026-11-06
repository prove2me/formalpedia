-- Prove2me | solution 1 for RH.Transport.Geometry.positive_part_le_subset
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:43.430205+00:00
-- url     : https://prove2.me/submissions/62509868-58df-46f7-a02d-5cb2b8d049c1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    max 0 (5 * ell p - 1 + d) ≤ d := by
  apply max_le
  · exact hd
  · unfold ell
    linarith
