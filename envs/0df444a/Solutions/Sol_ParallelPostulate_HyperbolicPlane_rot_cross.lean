-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.rot_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:07.103541+00:00
-- url     : https://prove2.me/submissions/c86e9ea9-c5f9-451b-acac-3c10ebf6ff02

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
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {c s : K} (h : c ^ 2 + s ^ 2 = 1) (A B C : K × K) :
    cross ((rot c s B).1 - (rot c s A).1, (rot c s B).2 - (rot c s A).2)
        ((rot c s C).1 - (rot c s A).1, (rot c s C).2 - (rot c s A).2)
      = cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) := by
  simp only [rot, cross]
  linear_combination ((B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)) * h
end ParallelPostulate.HyperbolicPlane
