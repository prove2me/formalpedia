-- Prove2me | solution 1 for PI.JetsPhW.Low.coeff_subst_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:14.764641+00:00
-- url     : https://prove2.me/submissions/312c8d2b-0638-4f72-852b-5efe0e9792f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_coeff_pow_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.Low
theorem _root_.solution {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries K) {e : σ →₀ ℕ} (he : e ≠ 0)
    (hd : Finsupp.degree e ≤ 2) :
    MvPowerSeries.coeff e (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff e A +
        PowerSeries.coeff 2 f * MvPowerSeries.coeff e (A ^ 2) := by
  classical
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hA)]
  rw [finsum_eq_sum_of_support_subset _ (s := ({1, 2} : Finset ℕ)) ?_]
  · rw [Finset.sum_pair (by norm_num), pow_one, smul_eq_mul, smul_eq_mul]
  · intro d hd'
    rw [Function.mem_support] at hd'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hc
    push Not at hc
    apply hd'
    rcases Nat.lt_or_ge d 3 with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, MvPowerSeries.coeff_one, if_neg he, smul_zero]
    · rw [coeff_pow_eq_zero hA d e (by omega), smul_zero]
end PI.JetsPhW.Low
