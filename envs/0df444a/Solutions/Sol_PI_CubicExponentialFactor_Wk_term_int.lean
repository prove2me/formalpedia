-- Prove2me | solution 1 for PI.CubicExponentialFactor.Wk.term_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:08.139376+00:00
-- url     : https://prove2.me/submissions/3951e17c-bacf-4ef4-8452-11afc2395ec5

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor
variable {p : ℕ} [Fact p.Prime]
namespace PI.CubicExponentialFactor.Wk
theorem _root_.solution {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {m k : ℕ} (hm : 1 ≤ m) {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ m * F)‖ ≤ 1 := by
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (PowerSeries.X ^ m) F,
    PowerSeries.coeff_mul_X_pow']
  split_ifs with h
  · rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) (hF _ (by omega))
  · simp
end PI.CubicExponentialFactor.Wk
