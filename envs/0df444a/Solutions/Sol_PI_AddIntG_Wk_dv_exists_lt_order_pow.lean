-- Prove2me | solution 1 for PI.AddIntG.Wk.dv_exists_lt_order_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:44.482693+00:00
-- url     : https://prove2.me/submissions/b2cc9442-6e29-4f8b-a963-451fcfae1c2d

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
theorem _root_.solution {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (N : ℕ) : ∃ m : ℕ, (N : ℕ∞) < (a ^ m).order := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨k * (N + 1), ?_⟩
  have h0 : MvPowerSeries.constantCoeff (a ^ k) = 0 := by rw [map_pow]; exact hk
  have := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (N + 1) h0
  rw [← pow_mul] at this
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) this
end PI.AddIntG.Wk
