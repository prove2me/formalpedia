-- Prove2me | solution 1 for PI.BiaddOfCubeWork.cc_Xv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:58.336046+00:00
-- url     : https://prove2.me/submissions/d6fad497-3f44-4b53-bacc-50bb4ef1211e

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
theorem _root_.solution (i : Fin 3) : MvPowerSeries.constantCoeff (Xv (p := p) i) = 0 := by
  exact MvPowerSeries.constantCoeff_X i
end PI.BiaddOfCubeWork
