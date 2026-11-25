-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_abs_log_eval_monomial_le_93b90b5d28e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:04.467882+00:00
-- url     : https://prove2.me/submissions/f23fd2d8-2369-4cba-8e6a-b9ef3327e0d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (m : ι →₀ ℕ) (c : ℂ) (u : ι → ℂ) :
    |Real.log ‖eval u (monomial m c)‖| ≤
      |Real.log ‖c‖| + ∑ i ∈ m.support, (m i : ℝ) * |Real.log ‖u i‖| := by
  have hnn : 0 ≤ |Real.log ‖c‖| + ∑ i ∈ m.support, (m i : ℝ) * |Real.log ‖u i‖| := by positivity
  rw [eval_monomial, Finsupp.prod]
  by_cases h : ∀ i ∈ m.support, u i ≠ 0
  · by_cases hc : c = 0
    · simpa [hc] using hnn
    · have hp : ∏ i ∈ m.support, u i ^ m i ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (h i hi)
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hp), norm_prod,
        Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (pow_ne_zero _ (h i hi)))]
      simp_rw [norm_pow, Real.log_pow]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [abs_mul, Nat.abs_cast]
  · push Not at h
    obtain ⟨i, hi, hu⟩ := h
    have : ∏ i ∈ m.support, u i ^ m i = 0 :=
      Finset.prod_eq_zero hi (by rw [hu]; exact zero_pow (Finsupp.mem_support_iff.mp hi))
    simpa [this] using hnn
end GroundTheory.Heights₂.Heights.LogInt
