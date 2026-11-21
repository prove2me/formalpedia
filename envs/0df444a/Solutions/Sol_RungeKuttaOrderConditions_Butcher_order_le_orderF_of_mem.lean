-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.order_le_orderF_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:21.631755+00:00
-- url     : https://prove2.me/submissions/74e29aa2-3ae6-4fc0-b22a-8c5de315d490

module
public import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution : ∀ {c : RTree} {F : Forest}, c ∈ F → order c ≤ orderF F := by
  intro c F
  induction F with
  | nil => simp
  | cons t ts ih =>
    intro h
    rcases List.mem_cons.1 h with rfl | h'
    · simp only [orderF]; omega
    · have hle := ih h'; simp only [orderF]; omega
end RungeKuttaOrderConditions.Butcher
