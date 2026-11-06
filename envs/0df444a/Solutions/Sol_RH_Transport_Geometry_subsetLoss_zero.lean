-- Prove2me | solution 1 for RH.Transport.Geometry.subsetLoss_zero
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:56.487128+00:00
-- url     : https://prove2.me/submissions/8993221d-7979-4864-a9bf-08414a61062d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : p < 1 / 30) :
    subsetLoss p 0 = 0 := by
  have hp' : p * 30 < 1 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < 30)).mp hp
  have hlt : (p * 30 - 1) / 6 < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by norm_num)
  have heq : 5 * (1 / 6 + p) - 1 = (p * 30 - 1) / 6 := by ring
  have h : 5 * (1 / 6 + p) - 1 ≤ 0 := heq ▸ hlt.le
  simp only [subsetLoss, ell, neg_zero, zero_add, add_zero]
  rw [max_eq_left h]
  norm_num
