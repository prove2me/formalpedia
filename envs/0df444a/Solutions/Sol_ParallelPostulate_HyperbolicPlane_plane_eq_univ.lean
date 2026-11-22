-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:58.357607+00:00
-- url     : https://prove2.me/submissions/a94caad8-4326-493a-97b0-8e34bfd20e8e

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} (hκ : 0 ≤ κ) : plane κ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have h : 0 ≤ κ * (p.1 ^ 2 + p.2 ^ 2) := mul_nonneg hκ (by positivity)
  rw [mem_plane]
  linarith
end ParallelPostulate.HyperbolicPlane
