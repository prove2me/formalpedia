-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_open_forward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:30.685077+00:00
-- url     : https://prove2.me/submissions/77248e1e-0bd8-4207-9d20-3e0972bfaddb

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_bound_along
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_quad_pos
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_eq_univ

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : K) (M : Dim K) (hM : M.zero ∈ plane κ) :
    ∃ t : K, 0 < t ∧ M.pt t ∈ plane κ := by
  rcases le_or_gt 0 κ with hκ | hκ
  · exact ⟨1, one_pos, by rw [plane_eq_univ hκ]; trivial⟩
  · obtain ⟨t, ht, h⟩ := quad_pos (1 + κ * (M.zero.1 ^ 2 + M.zero.2 ^ 2))
      (2 * κ * (M.zero.1 * M.dir.1 + M.zero.2 * M.dir.2))
      (-κ * (M.dir.1 ^ 2 + M.dir.2 ^ 2)) hM
      (mul_nonneg (by linarith) (by positivity))
    refine ⟨t, ht, ?_⟩
    rw [mem_plane, bound_along]
    exact h
end ParallelPostulate.HyperbolicPlane
