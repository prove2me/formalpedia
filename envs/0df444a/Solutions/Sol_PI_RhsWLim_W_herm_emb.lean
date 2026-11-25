-- Prove2me | solution 1 for PI.RhsWLim.W.herm_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:26.405539+00:00
-- url     : https://prove2.me/submissions/e911e14f-6109-4ee8-8325-88fe3a2816f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Theorems.Thm_PI_RhsWLim_W_herm_wb
import Theorems.Thm_PI_RhsWLim_W_wbPart_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (embWb k r μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  rw [herm_wb _ _ hz, wbPart_emb μ z' hz']
end PI.RhsWLim.W
