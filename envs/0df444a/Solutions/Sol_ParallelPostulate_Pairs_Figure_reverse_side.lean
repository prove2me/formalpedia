-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.reverse_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:38.968591+00:00
-- url     : https://prove2.me/submissions/736af4a8-8d63-4f23-98e3-534a83b5ee4c

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
theorem _root_.solution (F : Figure K) (P : K × K) : F.reverse.a.side P = -F.a.side P := by
  simp only [reverse, Dim.side, Dim.dir, cross]
  ring
end ParallelPostulate.Pairs.Figure
