-- Prove2me | solution 1 for PI.FglShared.logS_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:35:05.706539+00:00
-- url     : https://prove2.me/submissions/5a3e90b9-7c56-4a94-b034-b85ea879bcd4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Theorems.Thm_PI_FglShared_coeff_logS
import Theorems.Thm_P2M_PI_FglPhSplit_Wk_coeff_pow_eq_zero__60e911f4ed32
import Theorems.Thm_PI_FglPhSplit_Wk_deg_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglShared
theorem _root_.solution {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 1) :
    logS F = PowerSeries.subst (F - 1) (PowerSeries.log ℂ_[p]) := by
  have hF' : constantCoeff (F - 1) = 0 := by simp [hF]
  have ha : PowerSeries.HasSubst (F - 1) := PowerSeries.HasSubst.of_constantCoeff_zero hF'
  ext α
  rw [coeff_logS, PowerSeries.coeff_subst ha,
    finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ k => k) + 1)) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', PowerSeries.coeff_log, if_neg hn.ne', smul_eq_mul]
      simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
      ring
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hn
    have hdeg : Finsupp.degree α < n := by
      rw [← PI.FglPhSplit.Wk.deg_eq]
      omega
    rw [PI.FglPhSplit.Wk.coeff_pow_eq_zero' hF' hdeg, smul_zero]
end PI.FglShared
