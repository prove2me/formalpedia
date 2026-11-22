-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.one_parallel_iff_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:39.164181+00:00
-- url     : https://prove2.me/submissions/2b4737a2-9fc6-42a3-b453-3a7107d3d3ea

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_hyperbolic_two_parallels
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_euclid_one_parallel

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} {S : Set (K × K)} (hS : IsLine (plane κ) S)
    {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    (∃! M, IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅) ↔ 0 ≤ κ := by
  constructor
  · intro h
    by_contra hκ
    obtain ⟨M₁, M₂, hne, h₁, h₂⟩ := hyperbolic_two_parallels (not_le.mp hκ) hS hP hPS
    exact hne (h.unique h₁ h₂)
  · intro hκ
    exact euclid_one_parallel hκ hS hPS
end ParallelPostulate.HyperbolicPlane
