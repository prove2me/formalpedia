-- Prove2me | solution 1 for PI.JetsPhW.W.R.cc_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:11.536984+00:00
-- url     : https://prove2.me/submissions/09f0edcc-36b5-4267-83f3-a00225d5fc3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
open PI.JetsPhW.W.R
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.W.R
theorem _root_.solution {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h1 := PowerSeries.constantCoeff_subst (R := K) (PowerSeries.HasSubst.of_constantCoeff_zero' hex) l
  rw [hl] at h1
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  rw [finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
  simp only [pow_zero, map_one, smul_eq_mul, mul_one] at h1
  have h2 : PowerSeries.coeff 0 l = 0 := by
    rw [← h1]
    exact PowerSeries.constantCoeff_X
  simpa using h2
end PI.JetsPhW.W.R
