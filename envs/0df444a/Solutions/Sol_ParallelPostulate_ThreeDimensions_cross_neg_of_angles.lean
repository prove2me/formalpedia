-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.cross_neg_of_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:33.906973+00:00
-- url     : https://prove2.me/submissions/a7199e3f-9236-4cd2-a845-47fd559d4dcf

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
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    cross F.b.dir F.c.dir < 0 := by
  obtain ⟨hsin, hN, -, hβπ, -, hγπ⟩ := F.angle_facts hb hc
  rw [← hsin]
  have hneg : sin (angle (toE F.a.dir) (toE F.b.dir)
      + angle (toE (-F.a.dir)) (toE F.c.dir)) < 0 := by
    rw [← sin_sub_two_pi]
    exact sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  exact mul_neg_of_neg_of_pos hneg hN
end ParallelPostulate.ThreeDimensions
