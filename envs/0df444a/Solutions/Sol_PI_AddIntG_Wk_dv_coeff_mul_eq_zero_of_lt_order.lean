-- Prove2me | solution 1 for PI.AddIntG.Wk.dv_coeff_mul_eq_zero_of_lt_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:39.634801+00:00
-- url     : https://prove2.me/submissions/8d2c0c5d-9c0a-4be8-a734-c40fa1fb2ad4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder

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
theorem _root_.solution {R : Type*} [CommRing R] {σ : Type*} (f g : MvPowerSeries σ R)
    (e : σ →₀ ℕ) (h : (e.degree : ℕ∞) < f.order) : MvPowerSeries.coeff e (f * g) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le h (le_trans le_self_add MvPowerSeries.le_order_mul)
end PI.AddIntG.Wk
