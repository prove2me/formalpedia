-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.never_meet_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:32.45166+00:00
-- url     : https://prove2.me/submissions/39c6abb4-e9c7-4a30-a4c5-65bcf230a43c

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_eq_zero_of_angles
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_never_meet_of_two_right_angles


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π)
    (t u : ℝ) : F.b.pt t ≠ F.c.pt u :=
  F.never_meet_of_two_right_angles hc.ne' (cross_eq_zero_of_angles F hb hc hang) t u
end ParallelPostulate.ThreeDimensions
