-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.never_meet_of_two_right_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:05:03.509926+00:00
-- url     : https://prove2.me/submissions/0d35e96f-350b-4fe6-a80c-18e3af54f24e

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_c_one

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Pairs
variable {K : Type*} [CommRing K]
open ParallelPostulate.Pairs.Figure
namespace ParallelPostulate.Pairs.Figure
theorem _root_.solution (F : Figure K)
    (hc : F.a.side F.c.one ≠ 0) (hsum : cross F.b.dir F.c.dir = 0) (t u : K) :
    F.b.pt t ≠ F.c.pt u := by
  intro heq
  apply hc
  rw [F.side_c_one]
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at e1 e2 hsum ⊢
  linear_combination (-(F.c.one.2 - F.a.one.2)) * e1 + (F.c.one.1 - F.a.one.1) * e2 + t * hsum
end ParallelPostulate.Pairs.Figure
