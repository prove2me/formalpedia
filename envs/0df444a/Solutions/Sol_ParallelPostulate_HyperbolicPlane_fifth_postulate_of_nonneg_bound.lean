-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.fifth_postulate_of_nonneg_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:28.935465+00:00
-- url     : https://prove2.me/submissions/b85ec35f-1c40-4e4b-9e6a-4e799a78459d

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
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_b_one
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_c_one
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_b_pt
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_meet_eq
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_eq_univ

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} (hκ : 0 ≤ κ) (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.b.pt t ∈ plane κ ∧
      0 < F.a.side (F.b.pt t) := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : 0 < cross F.a.dir F.c.dir / cross F.b.dir F.c.dir := div_pos hc hsum
  refine ⟨_, _, ht, div_pos hb hsum, F.meet_eq hsum.ne', ?_, ?_⟩
  · rw [plane_eq_univ hκ]
    trivial
  · rw [F.side_b_pt]
    exact mul_pos ht hb
end ParallelPostulate.HyperbolicPlane
