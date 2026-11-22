-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.points_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:14:00.157509+00:00
-- url     : https://prove2.me/submissions/720ce6ae-2a2e-418e-ba8a-2af8b4d544ad

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
open ParallelPostulate.ThreeDimensions
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (M M' : Dim K) (hP : M.zero = M'.zero) (k : K)
    (hk : M.dir = (k * M'.dir.1, k * M'.dir.2)) : M.points ⊆ M'.points := by
  rintro _ ⟨t, rfl⟩
  refine ⟨t * k, ?_⟩
  have k1 := congrArg Prod.fst hk
  have k2 := congrArg Prod.snd hk
  have p1 := congrArg Prod.fst hP
  have p2 := congrArg Prod.snd hP
  simp only [Dim.dir] at k1 k2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination -p1 - t * k1
  · simp only [Dim.pt]
    linear_combination -p2 - t * k2
end ParallelPostulate.ThreeDimensions
