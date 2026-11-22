-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.sin_angle_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:29.922009+00:00
-- url     : https://prove2.me/submissions/3bd628ff-0a6e-4103-9385-6d99f589b5db

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_norm_toE_sq
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_norm_toE_neg
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_cos_angle_toE
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_sin_angle_toE
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_norm_toE_pos_left

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (a b c : ℝ × ℝ) (hab : 0 < cross a b) (hac : 0 < cross a c) :
    sin (angle (toE a) (toE b) + angle (toE (-a)) (toE c)) * (‖toE b‖ * ‖toE c‖)
      = cross b c := by
  have hA : 0 < ‖toE a‖ := norm_toE_pos_left hab.ne'
  have hA2 := norm_toE_sq a
  have hsβ := sin_angle_toE a b
  have hcβ := cos_angle_toE a b
  have hsγ := sin_angle_toE (-a) c
  have hcγ := cos_angle_toE (-a) c
  have hac' : cross (-a) c = -cross a c := by
    simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
  rw [abs_of_pos hab] at hsβ
  rw [hac', abs_neg, abs_of_pos hac, norm_toE_neg] at hsγ
  rw [norm_toE_neg] at hcγ
  simp only [Prod.fst_neg, Prod.snd_neg] at hcγ
  simp only [cross] at hsβ hsγ ⊢
  generalize angle (toE a) (toE b) = β at *
  generalize angle (toE (-a)) (toE c) = γ at *
  generalize ‖toE a‖ = A at *
  generalize ‖toE b‖ = B at *
  generalize ‖toE c‖ = C at *
  have hA2' : A ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hA2'
  rw [sin_add]
  linear_combination (cos γ * (A * C)) * hsβ + (a.1 * b.2 - a.2 * b.1) * hcγ
    + (sin γ * (A * C)) * hcβ + (a.1 * b.1 + a.2 * b.2) * hsγ
    - (b.1 * c.2 - b.2 * c.1) * hA2
end ParallelPostulate.ThreeDimensions
