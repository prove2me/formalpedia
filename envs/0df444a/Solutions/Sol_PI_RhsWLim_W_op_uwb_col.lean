-- Prove2me | solution 1 for PI.RhsWLim.W.op_uwb_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:01.137035+00:00
-- url     : https://prove2.me/submissions/a7f33bed-2e0e-4eb5-98b1-073379bcaa42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_op_not_mid_cases
import Theorems.Thm_PI_RhsWLim_W_MB_bvec_apply
import Theorems.Thm_PI_RhsWLim_W_MB_mulVec_bvec


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
theorem _root_.solution {g : Mat k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g l i = if l = i then 1 else 0 := by
  obtain ⟨a, rfl | rfl⟩ := op_not_mid_cases i hi
  · rw [← mulVec_bvec g (eI k r a) l, (hg.2 a).1, bvec_apply]
  · rw [← mulVec_bvec g (esI k r a) l, (hg.2 a).2, bvec_apply]
end PI.RhsWLim.W
