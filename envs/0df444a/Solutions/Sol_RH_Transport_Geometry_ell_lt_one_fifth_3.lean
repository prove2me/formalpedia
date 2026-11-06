-- Prove2me | solution 3 for RH.Transport.Geometry.ell_lt_one_fifth
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:57.207204+00:00
-- url     : https://prove2.me/submissions/74e1a306-beff-4e6d-8e61-6ddc79265b3a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : p < 1 / 30) : ell p < 1 / 5 := by
  unfold ell
  linarith
