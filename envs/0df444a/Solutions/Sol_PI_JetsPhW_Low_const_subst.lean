-- Prove2me | solution 1 for PI.JetsPhW.Low.const_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:29.397161+00:00
-- url     : https://prove2.me/submissions/e7735478-3897-4211-bda0-fe9b7d0116cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne

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
theorem _root_.solution {σ : Type*} {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst A f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hA)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [map_pow, hA, zero_pow hd, smul_zero]
end PI.JetsPhW.Low
