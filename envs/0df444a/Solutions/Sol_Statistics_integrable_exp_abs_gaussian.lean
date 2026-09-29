-- Prove2me | solution 1 for Statistics.integrable_exp_abs_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T17:34:51.502998+00:00
-- url     : https://prove2.me/submissions/c2dbbc62-d152-43f2-b465-f67b6e6e8c8d

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

section



open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace Statistics

/-- **The likelihood ratio of a Gaussian mean shift.**  Shifting the mean of a Gaussian by
`h` tilts it by the explicit exponential density `exp(h(r-m)/v - h²/(2v))`. -/
theorem gaussianReal_shift (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h : ℝ) :
    gaussianReal (m + h) v
      = (gaussianReal m v).withDensity
          (fun r => ENNReal.ofReal (rexp (h * (r - m) / v - h ^ 2 / (2 * v)))) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne v.coe_nonneg (fun hc => hv (by
    exact NNReal.coe_eq_zero.mp hc.symm))
  have hpt : ∀ r : ℝ, gaussianPDF (m + h) v r
      = gaussianPDF m v r * ENNReal.ofReal (rexp (h * (r - m) / v - h ^ 2 / (2 * v))) := by
    intro r
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 1
    simp only [gaussianPDFReal]
    have key : rexp (-(r - m) ^ 2 / (2 * (v : ℝ)))
          * rexp (h * (r - m) / (v : ℝ) - h ^ 2 / (2 * (v : ℝ)))
        = rexp (-(r - (m + h)) ^ 2 / (2 * (v : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [← key]
    ring
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv]
  have hG : Measurable (fun r : ℝ => ENNReal.ofReal
      (rexp (h * (r - m) / (v : ℝ) - h ^ 2 / (2 * (v : ℝ))))) := by fun_prop
  rw [← withDensity_mul _ (measurable_gaussianPDF m v) hG]
  congr 1
  funext r
  exact hpt r

/-- Every Gaussian has finite exponential moments of the absolute value. -/
theorem integrable_exp_abs_gaussian_aux (c m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => rexp (c * |x|)) (gaussianReal m v) := by
  have h1 : Integrable (fun x : ℝ => rexp (|c| * x)) (gaussianReal m v) :=
    integrable_exp_mul_gaussianReal _
  have h2 : Integrable (fun x : ℝ => rexp (-|c| * x)) (gaussianReal m v) :=
    integrable_exp_mul_gaussianReal _
  refine Integrable.mono (h1.add h2) (by fun_prop) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity : (0:ℝ) <
    rexp (|c| * x) + rexp (-|c| * x))]
  rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
  · have : c * |x| ≤ |c| * x := by
      rw [hx]; exact mul_le_mul_of_nonneg_right (le_abs_self c) (by rw [← hx]; positivity)
    have := Real.exp_le_exp.2 this
    linarith [Real.exp_pos (-|c| * x)]
  · have : c * |x| ≤ -|c| * x := by
      rw [hx]
      have : c * -x ≤ |c| * -x := mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
      linarith
    have := Real.exp_le_exp.2 this
    linarith [Real.exp_pos (|c| * x)]

/-- The exponential moment of a Gaussian is finite as an `ℝ≥0∞`-integral. -/
theorem lintegral_exp_abs_gaussian_lt_top (c m : ℝ) (v : ℝ≥0) :
    ∫⁻ x : ℝ, ENNReal.ofReal (rexp (c * |x|)) ∂(gaussianReal m v) < ⊤ := by
  have h := integrable_exp_abs_gaussian_aux c m v
  have := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    at this
  exact this

end Statistics

end

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem solution (c m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => rexp (c * |x|)) (gaussianReal m v) :=
  Statistics.integrable_exp_abs_gaussian_aux c m v
