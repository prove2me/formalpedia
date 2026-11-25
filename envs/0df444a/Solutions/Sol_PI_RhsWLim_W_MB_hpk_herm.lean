-- Prove2me | solution 1 for PI.RhsWLim.W.MB.hpk_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:25.713049+00:00
-- url     : https://prove2.me/submissions/24687ddf-6a5d-4c8c-b460-c0d803980d8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem

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
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply]
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp
end PI.RhsWLim.W.MB
