-- Prove2me | solution 1 for PI.JetsPhW.Low.coeff_subst_of_degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:01.494063+00:00
-- url     : https://prove2.me/submissions/b78ed153-b792-4627-a588-a5ce88d4ac90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_coeff_pow_eq_zero
import Theorems.Thm_PI_JetsPhW_Low_coeff_subst_low

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
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries K) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff e A := by
  have he : e ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact absurd hd (by norm_num)
  rw [coeff_subst_low hA f he (by omega), coeff_pow_eq_zero hA 2 e (by omega), mul_zero, add_zero]
end PI.JetsPhW.Low
