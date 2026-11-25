-- Prove2me | solution 1 for PI.JetsPhW.Ch.coeff_subst_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:42.611805+00:00
-- url     : https://prove2.me/submissions/024b2d5f-bf74-4488-9f6b-05fcde97d45e

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Theorems.Thm_PI_JetsPhW_Ch_coeff_pow_eq_zero_of_degree_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.JetsPhW
open PI PI.JetsPhW PI.JetsPhW.Ch
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.JetsPhW.Ch
theorem _root_.solution {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {f g : PowerSeries R} {N : ℕ} (hfg : ∀ k < N, PowerSeries.coeff k f = PowerSeries.coeff k g)
    {e : σ →₀ ℕ} (he : e.degree < N) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) = MvPowerSeries.coeff e (PowerSeries.subst a g) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k < N
  · rw [hfg k hk]
  · rw [coeff_pow_eq_zero_of_degree_lt ha (lt_of_lt_of_le he (not_lt.mp hk)), smul_zero, smul_zero]
end PI.JetsPhW.Ch
