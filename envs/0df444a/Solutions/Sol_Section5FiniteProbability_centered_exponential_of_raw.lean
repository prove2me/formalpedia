-- Prove2me | solution 1 for Section5FiniteProbability.centered_exponential_of_raw
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:39.159549+00:00
-- url     : https://prove2.me/submissions/1925b8d8-7398-443f-8ff5-2b75825ab6bc

import Mathlib
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory
theorem solution {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hraw : (∫ x, Real.exp (|Y x|/512) ∂μ) ≤ 130/127)
    (hmean : |∫ x, Y x ∂μ| ≤ 3) :
    (∫ x, Real.exp (|Y x-(∫ y, Y y ∂μ)|/512) ∂μ) ≤ 2 := by
  have hpt (x : Ω) : Real.exp (|Y x-(∫ y, Y y ∂μ)|/512) ≤
      Real.exp (3/512)*Real.exp (|Y x|/512) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := abs_sub (Y x) (∫ y, Y y ∂μ)
    linarith
  have hsmall : Real.exp (3/512 : ℝ) ≤ 512/509 := by
    convert Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 3/512)
      (by norm_num : (3/512 : ℝ) < 1) using 1 <;> norm_num
  calc
    _ ≤ ∫ x, Real.exp (3/512)*Real.exp (|Y x|/512) ∂μ :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite) hpt
    _ = Real.exp (3/512)*(∫ x, Real.exp (|Y x|/512) ∂μ) := integral_const_mul _ _
    _ ≤ (512/509)*(130/127) := mul_le_mul hsmall hraw
      (integral_nonneg (fun x => (Real.exp_pos _).le)) (by norm_num)
    _ ≤ 2 := by norm_num
