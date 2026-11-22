-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.law_of_sines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:25.004473+00:00
-- url     : https://prove2.me/submissions/016535fd-aad1-4ead-9b03-3f6994f5774b

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_angleFigure_side_b
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_angleFigure_side_c
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_angleFigure_cross
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_meet_eq
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_b_one
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_c_one


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (β γ : ℝ) (h : sin (β + γ) ≠ 0) :
    (angleFigure β γ).b.pt (sin γ / sin (β + γ))
      = (angleFigure β γ).c.pt (sin β / sin (β + γ)) := by
  have hc : cross (angleFigure β γ).a.dir (angleFigure β γ).c.dir = sin γ := by
    rw [← Figure.side_c_one, angleFigure_side_c]
  have hb : cross (angleFigure β γ).a.dir (angleFigure β γ).b.dir = sin β := by
    rw [← Figure.side_b_one, angleFigure_side_b]
  have hne : cross (angleFigure β γ).b.dir (angleFigure β γ).c.dir ≠ 0 := by
    rw [angleFigure_cross]; exact h
  have hmeet := (angleFigure β γ).meet_eq hne
  rw [hc, hb, angleFigure_cross] at hmeet
  exact hmeet
end ParallelPostulate.ThreeDimensions
