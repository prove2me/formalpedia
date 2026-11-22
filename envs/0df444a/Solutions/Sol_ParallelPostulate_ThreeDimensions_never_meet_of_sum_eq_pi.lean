-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.never_meet_of_sum_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:31.05911+00:00
-- url     : https://prove2.me/submissions/b1b6b1c7-d329-48da-a181-a29e849b7146

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_angleFigure_side_c
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_angleFigure_cross
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_never_meet_of_two_right_angles


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (β γ : ℝ) (hγ : 0 < γ) (hγ' : γ < π) (h : β + γ = π)
    (t u : ℝ) : (angleFigure β γ).b.pt t ≠ (angleFigure β γ).c.pt u := by
  apply Figure.never_meet_of_two_right_angles
  · rw [angleFigure_side_c]
    exact (sin_pos_of_pos_of_lt_pi hγ hγ').ne'
  · rw [angleFigure_cross, h, sin_pi]
end ParallelPostulate.ThreeDimensions
