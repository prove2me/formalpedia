-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.ne_of_side_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:11.425375+00:00
-- url     : https://prove2.me/submissions/33a1f9e3-77ea-45e4-91c4-edafbcf81969

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
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {X Y Z : ℝ × ℝ} (h : (Dim.mk X Y).side Z ≠ 0) :
    X ≠ Y ∧ Z ≠ X ∧ Z ≠ Y := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply h
    simp [Dim.side, Dim.dir, cross]
  · rintro rfl
    apply h
    simp [Dim.side, Dim.dir, cross]
  · rintro rfl
    apply h
    simp only [Dim.side, Dim.dir, cross]
    ring
end ParallelPostulate.HyperbolicPlane
