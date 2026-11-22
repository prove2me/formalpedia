-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:22.88386+00:00
-- url     : https://prove2.me/submissions/cb9d5524-e22c-4bcc-be54-f7e79031021a

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) :
    Set.BijOn (shift κ a w) (plane κ) (plane κ) := by
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by
    rw [hw]
    ring
  refine ⟨fun p hp => shift_mem_plane hκ hw hw0 hp, ?_, ?_⟩
  · intro p hp q hq h
    have h' := congrArg (shift κ (-a) w) h
    rwa [shift_neg_shift hκ hw hw0 hp, shift_neg_shift hκ hw hw0 hq] at h'
  · intro q hq
    refine ⟨shift κ (-a) w q, shift_mem_plane hκ hw' hw0 hq, ?_⟩
    have h := shift_neg_shift hκ hw' hw0 hq
    rwa [neg_neg] at h
end ParallelPostulate.HyperbolicPlane
