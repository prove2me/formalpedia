-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.sq_add_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:59.316179+00:00
-- url     : https://prove2.me/submissions/317b5868-cfc9-4560-9b35-3627ad8f14b2

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
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {v : K × K} (hv : v ≠ (0, 0)) : 0 < v.1 ^ 2 + v.2 ^ 2 := by
  by_contra h
  have hle : v.1 ^ 2 + v.2 ^ 2 ≤ 0 := not_lt.mp h
  have h1 : v.1 ^ 2 = 0 := by linarith [sq_nonneg v.1, sq_nonneg v.2]
  have h2 : v.2 ^ 2 = 0 := by linarith [sq_nonneg v.1, sq_nonneg v.2]
  exact hv (Prod.ext ((pow_eq_zero_iff two_ne_zero).mp h1) ((pow_eq_zero_iff two_ne_zero).mp h2))
end ParallelPostulate.HyperbolicPlane
