-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-09T23:52:36.453871+00:00
-- url     : https://prove2.me/submissions/0a6e089c-4d85-41fe-a804-fbd36574ce62

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (r : ℝ) (m : Measure ℝ) [IsFiniteMeasure m] :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} m := by
  have hm : MeasurableSet {x : ℝ | |x| < r} := measurableSet_lt (by fun_prop) measurable_const
  refine Measure.integrableOn_of_bounded (M := r ^ 2) (measure_ne_top _ _) (by fun_prop) ?_
  refine (ae_restrict_iff' hm).2 (Filter.Eventually.of_forall ?_)
  intro x hx
  have hx' : |x| < r := hx
  have h0 : 0 ≤ |x| := abs_nonneg x
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ r ^ 2 := (pow_lt_pow_left₀ hx' h0 two_ne_zero).le
