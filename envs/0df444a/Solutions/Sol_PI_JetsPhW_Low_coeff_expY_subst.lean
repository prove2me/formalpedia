-- Prove2me | solution 1 for PI.JetsPhW.Low.coeff_expY_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:50.675782+00:00
-- url     : https://prove2.me/submissions/c1687e66-19cf-4f5a-bfd3-093acbf77fb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_coeff_subst_of_degree_eq_one
import Theorems.Thm_PI_JetsPhW_Low_degree_expY

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
    MvPowerSeries.coeff E1 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E1 A :=
  coeff_subst_of_degree_eq_one hA f degree_expY
end PI.JetsPhW.Low
