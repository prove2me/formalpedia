-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.rot_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:34.430576+00:00
-- url     : https://prove2.me/submissions/89252702-c240-41a7-8fbd-cd0782bb10f0

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
omit [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) :
    Set.BijOn (rot c s) (plane κ) (plane κ) := by
  have h' : c ^ 2 + (-s) ^ 2 = 1 := by
    rw [← h]
    ring
  refine ⟨fun p hp => (rot_mem_plane h).mpr hp, ?_, ?_⟩
  · intro p _ q _ hpq
    have h2 := congrArg (rot c (-s)) hpq
    rwa [rot_rot_neg h, rot_rot_neg h] at h2
  · intro q hq
    refine ⟨rot c (-s) q, (rot_mem_plane h').mpr hq, ?_⟩
    have h2 := rot_rot_neg h' q
    rwa [neg_neg] at h2
end ParallelPostulate.HyperbolicPlane
