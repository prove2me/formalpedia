-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.cross_pos_of_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:32.964412+00:00
-- url     : https://prove2.me/submissions/4e518c5d-34c3-4c2f-a6df-124d33ee98a9

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
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_angle_facts

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
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    0 < cross F.b.dir F.c.dir := by
  obtain ⟨hsin, hN, hβ0, -, hγ0, -⟩ := F.angle_facts hb hc
  rw [← hsin]
  exact mul_pos (sin_pos_of_pos_of_lt_pi (by linarith) hang) hN
end ParallelPostulate.ThreeDimensions
