-- Prove2me | solution 1 for cdfVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:29:59.814622+00:00
-- url     : https://prove2.me/submissions/57ed5d30-356c-4a57-94f0-bd3fedef59e8

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic


/-
  Definition of expectation and variance in terms of Riemann-Stieltjes integral.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section


theorem solution (a b : ℝ) (F : ℝ → ℝ)
    (h_int_exp : RSIntegrable (fun x => x) F a b)
    (h_int_var : RSIntegrable (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b) :
    0 ≤ cdfVariance a b F h_int_exp h_int_var := by
  -- Unfold the definition of variance to expose the integral
  unfold cdfVariance

  -- 1. Construct a proof that the zero function is integrable by multiplying the variance integrand by 0
  have h_zero_int : RSIntegrable (fun x => 0 * (x - cdfExpectation a b F h_int_exp)^2) F a b :=
    rsIntegrable_integrand_const_mul (c := 0) h_int_var

  -- 2. Prove that the integral of this zero function is exactly 0
  have h_zero_eval : rsIntegral (fun x => 0 * (x - cdfExpectation a b F h_int_exp)^2) F a b h_zero_int = 0 := by
    rw [rsIntegral_integrand_const_mul h_int_var]
    exact zero_mul _

  -- 3. Apply your monotonicity theorem: 0 * (x - μ)² ≤ (x - μ)²
  have h_mono : rsIntegral (fun x => 0 * (x - cdfExpectation a b F h_int_exp)^2) F a b h_zero_int ≤
      rsIntegral (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b h_int_var := by
    apply rsIntegral_integrand_mono h_zero_int h_int_var
    intro x _hx
    rw [zero_mul]
    -- Mathlib's built-in theorem that squares are non-negative
    exact sq_nonneg (x - cdfExpectation a b F h_int_exp)

  -- 4. Substitute `0` into the left side of our inequality
  rw [h_zero_eval] at h_mono
  exact h_mono
end  -- noncomputable section

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

-----------------------------------------------------------------------------
-- 1. BASE CASE: The Zero Integrator (Required for Finset Induction)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 2. FINITE SUM INDUCTION (Bridging Thm 1.3 to arbitrary m)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 3. THE ANALYTIC STEP FUNCTION HELPER
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 4. THE MAIN RESULT: Expectation of discreteCDF is a finite sum
-----------------------------------------------------------------------------

end DiscreteExpectation  -- namespace
end DiscreteExpectation  -- section

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation  -- namespace
end ContinuousExpectation    -- section
