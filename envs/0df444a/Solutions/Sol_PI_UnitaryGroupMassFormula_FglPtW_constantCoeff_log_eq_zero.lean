-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FglPtW.constantCoeff_log_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:13.196484+00:00
-- url     : https://prove2.me/submissions/2a7e4160-352d-47cb-a7be-d247a023623c

import Definitions.Def_Formalism_PeriodIntegrals_FglPtW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffLogEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FglPtW
open PI.FglPtW
namespace PI.UnitaryGroupMassFormula.FglPtW
theorem _root_.solution {K : Type} [CommRing K] {l ex : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have h := congrArg MvPowerSeries.constantCoeff hlex
  rw [PowerSeries.constantCoeff_subst hex, finsum_eq_single _ 0] at h
  · have h' := h.trans PowerSeries.constantCoeff_X
    simpa using h'
  · intro d hd
    have : MvPowerSeries.constantCoeff (ex ^ d) = 0 := by
      rw [map_pow]
      have h0' : MvPowerSeries.constantCoeff ex = 0 := h0
      rw [h0', zero_pow hd]
    rw [this, smul_zero]
end PI.UnitaryGroupMassFormula.FglPtW
