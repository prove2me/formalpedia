-- Prove2me | solution 1 for PI.RhsWLim.W.MB.emb_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:44.181797+00:00
-- url     : https://prove2.me/submissions/41c8659b-9b2c-42d2-b4cd-11a50169ab19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_Hpk_Em
import Theorems.Thm_PI_RhsWLim_W_MB_sandwich
import Theorems.Thm_PI_RhsWLim_W_MB_emb_conjT
import Theorems.Thm_PI_RhsWLim_W_MB_EmT_Hpk

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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.MB
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.MB
theorem _root_.solution (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (embWb k r a)ᴴ * Hpk k r * embWb k r a =
      Em k r * (aᴴ * Hb k * a) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * Hpk k r * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_conjT]
  exact sandwich _ _ _ _ Hpk_Em EmT_Hpk
end PI.RhsWLim.W.MB
