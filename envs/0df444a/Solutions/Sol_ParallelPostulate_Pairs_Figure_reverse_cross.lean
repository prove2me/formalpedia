-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.reverse_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:44.040211+00:00
-- url     : https://prove2.me/submissions/bae8cdf3-6c41-43a1-bf19-63ff1971b65d

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
theorem _root_.solution (F : Figure K) :
    cross F.reverse.b.dir F.reverse.c.dir = -cross F.b.dir F.c.dir := by
  simp only [reverse, cross]
  ring
end ParallelPostulate.Pairs.Figure
