-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.strictBetween_of_between_pt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:14.372146+00:00
-- url     : https://prove2.me/submissions/3961c5f5-7aaa-4121-bb60-ad2fd13a7f14

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
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_injective

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (M : Dim ℝ) (hM : M.zero ≠ M.one) {a b c : ℝ}
    (h : Between (M.pt a) (M.pt c) (M.pt b)) : StrictBetween a c b := by
  obtain ⟨hne, u, hu0, hu1, hu⟩ := h
  have hc : c = a + u * (b - a) := by
    apply M.pt_injective hM
    rw [← hu]
    apply Prod.ext
    · simp only [Dim.pt]
      ring
    · simp only [Dim.pt]
      ring
  have hab : a ≠ b := fun e => hne (by rw [e])
  rcases lt_or_gt_of_ne hab with h | h
  · left
    constructor <;> nlinarith
  · right
    constructor <;> nlinarith
end ParallelPostulate.HyperbolicPlane
