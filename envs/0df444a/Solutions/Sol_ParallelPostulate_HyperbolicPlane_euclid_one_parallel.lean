-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.euclid_one_parallel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:10:33.193249+00:00
-- url     : https://prove2.me/submissions/ccd8590f-3dd5-44bc-a139-bbccfddd3469

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_one_parallel_of_all_within
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_eq_univ

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} (hκ : 0 ≤ κ) {S : Set (K × K)} (hS : IsLine (plane κ) S)
    {P : K × K} (hPS : P ∉ S) : ∃! M, IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅ := by
  obtain ⟨L, hL, rfl, -⟩ := hS
  have hP : P ∈ plane κ := by
    rw [plane_eq_univ hκ]
    trivial
  have hPL : P ∉ L.points := fun h => hPS ⟨h, hP⟩
  exact one_parallel_of_all_within (plane κ) L hL hP hPL
    (fun t => by rw [plane_eq_univ hκ]; trivial)
end ParallelPostulate.HyperbolicPlane
