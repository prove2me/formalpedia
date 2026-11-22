-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.other_side_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:43.193571+00:00
-- url     : https://prove2.me/submissions/7e99e3cd-80c4-4e4d-bcb2-c22c6a963506

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_the_other_side
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_neg_of_angles

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
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 :=
  meet_on_the_other_side F hb hc (cross_neg_of_angles F hb hc hang)
end ParallelPostulate.ThreeDimensions
