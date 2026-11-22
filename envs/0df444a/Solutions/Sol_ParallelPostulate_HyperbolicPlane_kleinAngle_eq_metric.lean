-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.kleinAngle_eq_metric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:50.514888+00:00
-- url     : https://prove2.me/submissions/3bb873b8-8eda-4736-85a4-9ea0d12c8164

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinMetric_sub
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) (A B : ℝ × ℝ) :
    kleinAngle κ P A B = arccos (kleinMetric κ P (A - P) (B - P)
      / (√(kleinMetric κ P (A - P) (A - P)) * √(kleinMetric κ P (B - P) (B - P)))) := by
  have hm : 0 < 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 :=
    one_div_pos.mpr (pow_pos (mem_plane.mp hP) 2)
  have e1 : kleinMetric κ P (A - P) (B - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 * 1 * kleinInner κ P A B := by
    rw [kleinMetric_sub]
    ring
  have e2 : kleinMetric κ P (A - P) (A - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 ^ 2 * kleinInner κ P A A := by
    rw [kleinMetric_sub]
    ring
  have e3 : kleinMetric κ P (B - P) (B - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 ^ 2 * kleinInner κ P B B := by
    rw [kleinMetric_sub]
    ring
  rw [kleinAngle, e1, e2, e3, kleinAngle_aux hm (by norm_num : (0 : ℝ) < 1 * 1)]
end ParallelPostulate.HyperbolicPlane
