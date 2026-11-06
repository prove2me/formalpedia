-- Prove2me | solution 1 for ProbabilityTheory.cnd_levyCompensatedIntegrand_fixed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:12:21.053841+00:00
-- url     : https://prove2.me/submissions/446aceb6-4563-43d8-9b27-a349ea0c6a91

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_isPositiveDefinite_exp_ofReal_mul
import Theorems.Thm_ProbabilityTheory_IsPositiveDefinite_cnd_sub_one
import Theorems.Thm_ProbabilityTheory_cnd_imag_linear
import Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_def
import Theorems.Thm_ProbabilityTheory_IsConditionallyNegativeDefinite_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal BigOperators

theorem solution (x : ℝ) :
    IsConditionallyNegativeDefinite (fun ξ => levyCompensatedIntegrand ξ x) := by
  have hexp : IsConditionallyNegativeDefinite
      (fun ξ => Complex.exp ((x : ℂ) * (ξ : ℂ) * I) - 1) :=
    (isPositiveDefinite_exp_ofReal_mul x).cnd_sub_one
  have hlin : IsConditionallyNegativeDefinite
      (fun ξ => ((if |x| < 1 then -x else 0 : ℝ) : ℂ) * ↑ξ * I) :=
    cnd_imag_linear _
  have key : (fun ξ => levyCompensatedIntegrand ξ x)
      = fun ξ : ℝ => (Complex.exp ((x : ℂ) * ↑ξ * I) - 1)
          + ((if |x| < 1 then -x else 0 : ℝ) : ℂ) * ↑ξ * I := by
    funext ξ
    simp only [levyCompensatedIntegrand_def]
    by_cases hx : |x| < 1
    · simp only [if_pos hx]
      push_cast
      ring
    · simp only [if_neg hx]
      push_cast
      ring
  rw [key]
  exact hexp.add hlin
