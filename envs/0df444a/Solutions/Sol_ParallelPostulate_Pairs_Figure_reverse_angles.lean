-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.reverse_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:11:52.745189+00:00
-- url     : https://prove2.me/submissions/fc689cd6-a524-4f01-add7-ffc363641b0f

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
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_dir


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
namespace _root_.ParallelPostulate.Pairs.Figure
theorem _root_.solution (F : Figure ℝ) :
    angle (toE F.reverse.a.dir) (toE F.reverse.b.dir)
        + angle (toE (-F.reverse.a.dir)) (toE F.reverse.c.dir)
      = angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) := by
  rw [F.reverse_dir, neg_neg]
  change angle (toE (-F.a.dir)) (toE F.c.dir) + angle (toE F.a.dir) (toE F.b.dir)
    = angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)
  ring
end _root_.ParallelPostulate.Pairs.Figure
end ParallelPostulate.ThreeDimensions
