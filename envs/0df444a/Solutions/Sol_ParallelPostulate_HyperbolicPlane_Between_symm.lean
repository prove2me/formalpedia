-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.Between.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:04:24.517777+00:00
-- url     : https://prove2.me/submissions/4e45424a-3cb1-47f3-be95-b877a8772a1b

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
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
namespace Between
theorem _root_.solution {A B C : K × K} (h : Between A B C) : Between C B A := by
  obtain ⟨hAC, u, h0, h1, rfl⟩ := h
  refine ⟨hAC.symm, 1 - u, by linarith, by linarith, ?_⟩
  apply Prod.ext
  · simp only [Dim.pt]
    ring
  · simp only [Dim.pt]
    ring
end Between
end ParallelPostulate.HyperbolicPlane
