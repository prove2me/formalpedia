-- Prove2me | solution 1 for PI.BiaddOfCubeWork.simeq_of_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:58.328314+00:00
-- url     : https://prove2.me/submissions/d613b38b-a387-4c04-a508-09a952f0e99a

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
theorem _root_.solution {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (hs : Simeq f' g') : Simeq f g := by
  show MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
  rw [e]
  exact hs
end PI.BiaddOfCubeWork
