-- Prove2me | solution 1 for PI.CubicExponentialFactor.Wk.term_int1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:07.721849+00:00
-- url     : https://prove2.me/submissions/d201bf70-823f-4f5f-9b3d-a665ffe719d9

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
import Theorems.Thm_PI_CubicExponentialFactor_Wk_term_int

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
theorem _root_.solution {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {k : ℕ} {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * F)‖ ≤ 1 := by
  have h := term_int ha (m := 1) le_rfl hF
  rwa [pow_one] at h
end PI.CubicExponentialFactor.Wk
