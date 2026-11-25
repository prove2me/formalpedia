-- Prove2me | solution 1 for PI.JetsPhW.Low.coeff_expX_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:47.588232+00:00
-- url     : https://prove2.me/submissions/1790dedb-b027-4c6d-b414-63f6c098e7ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_coeff_subst_of_degree_eq_one
import Theorems.Thm_PI_JetsPhW_Low_degree_expX

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
    MvPowerSeries.coeff E0 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E0 A :=
  coeff_subst_of_degree_eq_one hA f degree_expX
end PI.JetsPhW.Low
