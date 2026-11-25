-- Prove2me | solution 1 for PI.RhsWLim.W.op_fix_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:04.46163+00:00
-- url     : https://prove2.me/submissions/f50fcc5b-cccf-400a-bfa4-d76d8ce39790

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI

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
theorem _root_.solution {g : Mat k r} (hg : g ∈ UH (Hpk k r)) {f : Fin (2 * r + k + 1) → ℂ} (hf : g *ᵥ f = f) :
    gᴴ *ᵥ (Hpk k r *ᵥ f) = Hpk k r *ᵥ f := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc gᴴ *ᵥ (Hpk k r *ᵥ f) = gᴴ *ᵥ (Hpk k r *ᵥ (g *ᵥ f)) := by rw [hf]
    _ = (gᴴ * Hpk k r * g) *ᵥ f := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = Hpk k r *ᵥ f := by rw [hg']
end PI.RhsWLim.W
