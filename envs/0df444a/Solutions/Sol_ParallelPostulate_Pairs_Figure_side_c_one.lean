-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.side_c_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:35.31573+00:00
-- url     : https://prove2.me/submissions/935f3328-7c43-4429-bc70-a4cc482b7b92

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
theorem _root_.solution (F : Figure K) : F.a.side F.c.one = cross F.a.dir F.c.dir := by
  simp only [Dim.side, Dim.dir, cross, ← F.a1_eq_c0]
  ring
end ParallelPostulate.Pairs.Figure
