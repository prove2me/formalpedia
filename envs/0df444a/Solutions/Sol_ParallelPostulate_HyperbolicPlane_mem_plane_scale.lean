-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.mem_plane_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:25.78666+00:00
-- url     : https://prove2.me/submissions/6d134947-4ed3-4723-968d-8db5cc927f99

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
omit [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ s : K) (p : K × K) :
    p ∈ plane (κ * s ^ 2) ↔ (s * p.1, s * p.2) ∈ plane κ := by
  rw [mem_plane, mem_plane]
  have e : 1 + κ * s ^ 2 * (p.1 ^ 2 + p.2 ^ 2) = 1 + κ * ((s * p.1) ^ 2 + (s * p.2) ^ 2) := by
    ring
  rw [e]
end ParallelPostulate.HyperbolicPlane
