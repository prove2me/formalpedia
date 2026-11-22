-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_beyond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:58.287125+00:00
-- url     : https://prove2.me/submissions/77d431d1-39ac-4c04-95b8-14bae05a3d3f

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_dir_ne_zero
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_bound_along
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_quad_nonpos
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_sq_add_sq_pos
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} (hκ : κ < 0) (L : Dim K) (hL : L.zero ≠ L.one) :
    ∃ T : K, ∀ t : K, T ≤ t → L.pt t ∉ plane κ := by
  obtain ⟨T, hT⟩ := quad_nonpos (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
    (2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) (-κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2))
    (mul_pos (by linarith) (sq_add_sq_pos (L.dir_ne_zero hL)))
  refine ⟨T, fun t ht hmem => ?_⟩
  have h := hT t ht
  rw [← bound_along] at h
  exact absurd (mem_plane.mp hmem) (not_lt.mpr h)
end ParallelPostulate.HyperbolicPlane
