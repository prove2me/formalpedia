-- Prove2me | solution 1 for PI.JetsPhW.Low.coeff_expXY_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:47.783144+00:00
-- url     : https://prove2.me/submissions/6ea0165c-8d2a-406b-9ba2-0a7d61f35bb4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_coeff_subst_low
import Theorems.Thm_PI_JetsPhW_Low_degree_expXY
import Theorems.Thm_PI_JetsPhW_Low_expXY_ne_zero
import Theorems.Thm_PI_JetsPhW_Low_coeff_expXY_mul

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
theorem _root_.solution {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff bivariateExponentMonomial (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff bivariateExponentMonomial A +
        PowerSeries.coeff 2 f *
          (2 * (MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 A)) := by
  rw [coeff_subst_low hA f expXY_ne_zero (by rw [degree_expXY]), pow_two, coeff_expXY_mul hA hA]
  ring
end PI.JetsPhW.Low
