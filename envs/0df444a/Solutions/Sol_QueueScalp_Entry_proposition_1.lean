-- Prove2me | solution 1 for QueueScalp.Entry.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:25.81581+00:00
-- url     : https://prove2.me/submissions/f2e732c4-f93b-45cd-94ca-976373f03404

import Definitions.Def_QueueScalp_Entry_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Function
import Lean.Elab.Tactic.Omega
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

open QueueScalp.Entry

theorem solution (P : Params) (hS : P.Standing) (lam : ℝ)
    (hlam : 0 < lam) (hstable : lam < P.mu) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1,
      D P.mu lam q = (lam / P.mu) ^ 2 / (P.mu - lam + lam * q)) ∧
      StrictAntiOn (D P.mu lam) (Set.Icc (0 : ℝ) 1) := by
  have hform (q : ℝ) : D P.mu lam q = (lam / P.mu)^2 / (P.mu-lam+lam*q) := by
    unfold D W1 W2
    ring
  constructor
  · intro q hq
    exact hform q
  · intro a ha b hb hab
    rw [hform,hform]
    have hn : 0 < (lam / P.mu)^2 := sq_pos_of_pos (div_pos hlam hS.1)
    have hda : 0 < P.mu-lam+lam*a :=
      add_pos_of_pos_of_nonneg (sub_pos.mpr hstable) (mul_nonneg hlam.le ha.1)
    have hdb : P.mu-lam+lam*a < P.mu-lam+lam*b := by nlinarith
    exact div_lt_div_of_pos_left hn hda hdb


