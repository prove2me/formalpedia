-- Prove2me | solution 1 for P2M_Formalism_ExtensionFiltration_period_bound__2065990858fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:12.115544+00:00
-- url     : https://prove2.me/submissions/c0357c1a-9fd2-406f-9919-a965ad4bcb6e

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ExtensionFiltration
open Finset Module NumberField
namespace Formalism.ExtensionFiltration
theorem _root_.solution : PeriodBound := by
  intro logOm v rd Lc L x b a hlog hv hrd hLc hx hb ha
  have hrd0 : 0 < rd := by linarith
  have hv' : v = rd / 2 := by linarith
  have hpv : Real.pi / v = 2 * Real.pi / rd := by rw [hv', div_div_eq_mul_div]; ring
  have hl2pi : Real.log (2 * Real.pi / rd) = Real.log (2 * Real.pi) - Real.log rd :=
    Real.log_div (by positivity) hrd0.ne'
  have hlrd : 2 * Real.log 2 ≤ Real.log rd := by
    have h4 : Real.log 4 ≤ Real.log rd := Real.log_le_log (by norm_num) hrd
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      first | norm_num | skip
    linarith
  have hl2 := Real.log_two_gt_d9
  have hpi8 : Real.log (2 * Real.pi) ≤ 3 * Real.log 2 := by
    have h8 : Real.log (2 * Real.pi) ≤ Real.log 8 :=
      Real.log_le_log (by positivity) (by linarith [Real.pi_le_four])
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      first | norm_num | skip
    linarith
  have hpi0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hg1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos L
  have hlar : Real.log (a * rd) = Real.log x + L + Real.log rd := by
    rw [ha, Real.log_mul (mul_pos hx0 hb0).ne' hrd0.ne', Real.log_mul hx0.ne' hb0.ne', hb, Real.log_exp]
  rw [hlar, hlog, hpv, hl2pi]
  obtain ⟨hL1, hL2⟩ := abs_le.1 hLc
  rw [abs_le]
  constructor <;> linarith
end Formalism.ExtensionFiltration
