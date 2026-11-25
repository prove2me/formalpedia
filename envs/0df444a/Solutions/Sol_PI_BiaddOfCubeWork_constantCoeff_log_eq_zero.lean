-- Prove2me | solution 1 for PI.BiaddOfCubeWork.constantCoeff_log_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:06.24051+00:00
-- url     : https://prove2.me/submissions/45fc683a-1d7e-47ce-aa7a-1dd58381e494

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BiaddOfCube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BiaddOfCubeWork
open PI.BiaddOfCube
variable {p : ℕ} [Fact p.Prime]
namespace PI.BiaddOfCubeWork
theorem _root_.solution {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hex'
  have h1 := PowerSeries.constantCoeff_subst (R := ℂ_[p]) hs l
  rw [h, finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero]),
    pow_zero, map_one, smul_eq_mul, mul_one] at h1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1]
  exact PowerSeries.constantCoeff_X
end PI.BiaddOfCubeWork
