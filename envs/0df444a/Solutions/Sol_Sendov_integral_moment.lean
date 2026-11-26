-- Prove2me | solution 1 for Sendov.integral_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:02:45.888665+00:00
-- url     : https://prove2.me/submissions/82ee048f-5aca-40e6-955b-9e655f05a988

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Theorems.Thm_Sendov_intervalIntegrable_const_mul_pow
import Theorems.Thm_Sendov_t3_mul_Q_pow

set_option autoImplicit false
open Sendov
open MeasureTheory Finset
namespace Sendov
theorem _root_.solution (n : ℕ) (α : ℝ) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k) = mom n α k := by
  rw [mom]
  have hfun : (fun t : ℝ => t ^ 3 * Q n α t ^ k)
      = fun t : ℝ => ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
            * t ^ (2 * i - l + 3) :=
    funext fun t => t3_mul_Q_pow n α t k
  rw [hfun, intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun l _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      rw [one_pow]
      norm_num
      ring
    · exact fun l _ => intervalIntegrable_const_mul_pow _ _
  · intro i _
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_finsetSum _ fun l _ => by fun_prop
end Sendov
