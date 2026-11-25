-- Prove2me | solution 1 for PI.BiaddOfCubeWork.constantCoeff_subst_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:10.882141+00:00
-- url     : https://prove2.me/submissions/c0e46b6d-33fe-4018-88bd-09316952d6c6

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
variable {σ : Type*}
namespace PI.BiaddOfCubeWork
theorem _root_.solution {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero ha f hf
end PI.BiaddOfCubeWork
