-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.isIntegralAt_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:40.749341+00:00
-- url     : https://prove2.me/submissions/2bdf4e19-ba4c-4003-9bf1-b93c27f0e483

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution {x : ℂ_[p]} (hx : IsIntP x) : IsIntP (-x) := by
  show ‖-x‖ ≤ 1
  rw [norm_neg]
  exact hx
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
