-- Prove2me | solution 3 for RH.Transport.Geometry.positive_part_le_subset
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:59.113355+00:00
-- url     : https://prove2.me/submissions/940d217b-89b9-4cbd-a14a-35052464f534

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p d : ℝ} (hp : p < 1 / 30) (hd : 0 ≤ d) :
    max 0 (5 * ell p - 1 + d) ≤ d := by
  unfold ell
  apply max_le hd
  linarith
