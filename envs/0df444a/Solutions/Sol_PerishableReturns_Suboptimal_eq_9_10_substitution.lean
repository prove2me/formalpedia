-- Prove2me | solution 1 for PerishableReturns.Suboptimal.eq_9_10_substitution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:27:00.895976+00:00
-- url     : https://prove2.me/submissions/72d58d25-1050-4bac-853b-cc5e944a97f2

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

set_option autoImplicit false
open PerishableReturns.Suboptimal
open MeasureTheory ProbabilityTheory

theorem solution (K : Costs) (c1 c2 R : ℝ)
    (hpolicy : K.Admissible c1 c2 R) (D : Measure ℝ) (hD : IsDemand D)
    [NullSingletonClass D] (Q : ℝ)
    (hQ : cdf D Q = (K.p + K.g2 - K.c) / (K.p + K.g2 - K.c3)) :
    (0 = -c1 + K.p + K.g - cdf D Q * (K.p + K.g - c2) -
      cdf D ((1 - R) * Q) * ((1 - R) * (c2 - K.c3))) ↔
    (0 = (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3) +
      cdf D ((1 - R) * Q) * ((1 - R) * (c2 - K.c3))) := by
  have h1 : (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3)
      = cdf D Q * (K.p + K.g - c2) := by
    rw [hQ, div_mul_eq_mul_div]
  rw [h1]
  constructor <;> intro h <;> linarith
