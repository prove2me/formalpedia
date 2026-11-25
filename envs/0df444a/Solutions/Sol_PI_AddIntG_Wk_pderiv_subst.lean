-- Prove2me | solution 1 for PI.AddIntG.Wk.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:58.853049+00:00
-- url     : https://prove2.me/submissions/c62c8400-539f-452b-995a-3caac145d0de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Theorems.Thm_PI_AddIntG_Wk_dv_exists_lt_order_pow
import Theorems.Thm_PI_AddIntG_Wk_dv_coeff_mul_eq_zero_of_lt_order
import Theorems.Thm_PI_AddIntG_Wk_dv_pderiv_subst_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (f : PowerSeries R) (i : σ) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative R f) * MvPowerSeries.pderiv R i a := by
  rw [← sub_eq_zero]
  ext e
  rw [map_zero]
  obtain ⟨m, hm⟩ := dv_exists_lt_order_pow ha e.degree
  set g : PowerSeries R := PowerSeries.mk fun n => PowerSeries.coeff (n + m) f
  have hf : f = ((PowerSeries.trunc m f : Polynomial R) : PowerSeries R) + PowerSeries.X ^ m * g := by
    ext n
    rw [map_add, Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul']
    by_cases hn : n < m
    · simp [hn, not_le.mpr hn]
    · simp [hn, not_lt.mp hn, g, Nat.sub_add_cancel (not_lt.mp hn)]
  have key : MvPowerSeries.pderiv R i (PowerSeries.subst a f) -
      PowerSeries.subst a (PowerSeries.derivative R f) * MvPowerSeries.pderiv R i a =
      a ^ m * (MvPowerSeries.pderiv R i (PowerSeries.subst a g) -
        PowerSeries.subst a (PowerSeries.derivative R g) * MvPowerSeries.pderiv R i a) := by
    have hc : PowerSeries.subst a ((m : PowerSeries R)) = (m : MvPowerSeries σ R) := by
      rw [← map_natCast (PowerSeries.C (R := R)), PowerSeries.subst_C, map_natCast]
    conv_lhs => rw [hf]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      PowerSeries.derivative_X, mul_one]
    simp only [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha,
      PowerSeries.subst_X ha, hc]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      dv_pderiv_subst_coe ha]
    ring
  rw [key]
  exact dv_coeff_mul_eq_zero_of_lt_order _ _ e hm
end PI.AddIntG.Wk
