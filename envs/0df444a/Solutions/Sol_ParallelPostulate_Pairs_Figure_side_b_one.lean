-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.side_b_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:35.952735+00:00
-- url     : https://prove2.me/submissions/543e9b06-4868-40fd-adb4-223ea01e22a5

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

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Pairs
variable {K : Type*} [CommRing K]
open ParallelPostulate.Pairs.Figure
namespace ParallelPostulate.Pairs.Figure
theorem _root_.solution (F : Figure K) : F.a.side F.b.one = cross F.a.dir F.b.dir := by
  simp only [Dim.side, Dim.dir, F.a0_eq_b0]
end ParallelPostulate.Pairs.Figure
