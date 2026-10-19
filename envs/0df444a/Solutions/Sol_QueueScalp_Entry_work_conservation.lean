-- Prove2me | solution 1 for QueueScalp.Entry.work_conservation
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:23.108514+00:00
-- url     : https://prove2.me/submissions/83dadd9d-cc76-45c6-93ed-5ed9058e14a3

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

theorem solution (P : Params) (hS : P.Standing) (lam q : ℝ)
    (hlam : 0 ≤ lam) (hstable : lam < P.mu) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    q * W1 P.mu lam q + (1 - q) * W2 P.mu lam q = 1 / (P.mu - lam) := by
  unfold W1 W2
  ring


