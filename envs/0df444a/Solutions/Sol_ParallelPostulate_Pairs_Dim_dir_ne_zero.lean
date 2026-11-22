-- Prove2me | solution 1 for ParallelPostulate.Pairs.Dim.dir_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:25.369216+00:00
-- url     : https://prove2.me/submissions/431d3323-0cb8-4bf3-8466-9b8e830ccc2e

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
open ParallelPostulate.Pairs.Dim
namespace ParallelPostulate.Pairs.Dim
theorem _root_.solution (L : Dim K) (hL : L.zero ≠ L.one) : L.dir ≠ (0, 0) := by
  intro h0
  apply hL
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [dir] at h1 h2
  exact Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm
end ParallelPostulate.Pairs.Dim
