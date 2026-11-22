-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_stretch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:26.333706+00:00
-- url     : https://prove2.me/submissions/faf124af-59f5-4815-bba0-88e0dd1c903a

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
    ∃ T : K, ∀ t : K, L.pt t ∈ plane κ → -T < t ∧ t < T := by
  have hγ : 0 < -κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2) :=
    mul_pos (by linarith) (sq_add_sq_pos (L.dir_ne_zero hL))
  obtain ⟨T₁, h₁⟩ := quad_nonpos (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
    (2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) _ hγ
  obtain ⟨T₂, h₂⟩ := quad_nonpos (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
    (-(2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2))) _ hγ
  refine ⟨max T₁ T₂, fun t ht => ?_⟩
  rw [mem_plane, bound_along] at ht
  constructor
  · by_contra h
    have h' : T₂ ≤ -t := by
      have := not_lt.mp h
      linarith [le_max_right T₁ T₂]
    have h'' := h₂ (-t) h'
    have e : (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
        + -(2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) * -t
        - -κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2) * (-t) ^ 2
        = (1 + κ * (L.zero.1 ^ 2 + L.zero.2 ^ 2))
        + (2 * κ * (L.zero.1 * L.dir.1 + L.zero.2 * L.dir.2)) * t
        - -κ * (L.dir.1 ^ 2 + L.dir.2 ^ 2) * t ^ 2 := by ring
    rw [e] at h''
    linarith
  · by_contra h
    have h' : T₁ ≤ t := le_trans (le_max_left _ _) (not_lt.mp h)
    linarith [h₁ t h']
end ParallelPostulate.HyperbolicPlane
