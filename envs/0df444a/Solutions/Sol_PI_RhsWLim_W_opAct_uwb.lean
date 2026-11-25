-- Prove2me | solution 1 for PI.RhsWLim.W.opAct_uwb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:29.728251+00:00
-- url     : https://prove2.me/submissions/0b689b50-ff8e-49a7-a64e-7b10acbcf7c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_op_uwb_eq_emb
import Theorems.Thm_PI_RhsWLim_W_opAct_emb
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem


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
theorem _root_.solution {s : Mat k r} (hs : s ∈ UWb k r) :
    ∃ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k ∧ opAct k r s = blkAct k μ := by
  refine ⟨s.submatrix (wI k r) (wI k r), ?_, ?_⟩
  · rw [← emb_mem (r := r), ← op_uwb_eq_emb hs]
    exact hs.1
  · funext p
    conv_lhs => rw [op_uwb_eq_emb hs]
    exact opAct_emb _ p
end PI.RhsWLim.W
