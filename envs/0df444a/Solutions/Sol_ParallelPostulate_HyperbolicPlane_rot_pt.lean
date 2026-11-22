-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.rot_pt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:14:53.299053+00:00
-- url     : https://prove2.me/submissions/b6f3731f-9464-4c75-b113-f1557be89fc0

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
theorem _root_.solution (c s : K) (M : Dim K) (t : K) :
    rot c s (M.pt t) = (Dim.mk (rot c s M.zero) (rot c s M.one)).pt t := by
  apply Prod.ext
  · simp only [rot, Dim.pt]
    ring
  · simp only [rot, Dim.pt]
    ring
end ParallelPostulate.HyperbolicPlane
