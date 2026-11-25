-- Prove2me | solution 1 for PI.RhsWLim.W.hb_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:15.145894+00:00
-- url     : https://prove2.me/submissions/4757a521-6915-4f11-b42a-40702e7e9d3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_P2M_RH_PI_RhsWLim_W_hb_sq_31e4f0bb52828001

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) :
    (Hb k * μᴴ * Hb k) * μ = 1 := by
  calc (Hb k * μᴴ * Hb k) * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hμ, hb_sq]
end PI.RhsWLim.W
