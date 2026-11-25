-- Prove2me | solution 1 for PI.RhsWLim.W.op_uwb_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:24:42.859143+00:00
-- url     : https://prove2.me/submissions/fe488ffc-925d-49f5-91f7-14298a3d7604

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_op_not_mid_cases
import Theorems.Thm_PI_RhsWLim_W_op_hpk_e
import Theorems.Thm_PI_RhsWLim_W_op_hpk_es
import Theorems.Thm_PI_RhsWLim_W_op_fix_dual
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
    g i l = if i = l then 1 else 0 := by
  have key : ∀ j : Fin (2 * r + k + 1), gᴴ *ᵥ bvec j = bvec j → g j l = if j = l then 1 else 0 := by
    intro j hj
    have h := congrFun hj l
    rw [mulVec_bvec, bvec_apply, Matrix.conjTranspose_apply] at h
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : l = j
    · rw [if_pos e, if_pos e.symm, star_one]
    · rw [if_neg e, if_neg (fun e' => e e'.symm), star_zero]
  obtain ⟨a, rfl | rfl⟩ := op_not_mid_cases i hi
  · apply key
    have := op_fix_dual hg.1 (hg.2 a).2
    rwa [op_hpk_es] at this
  · apply key
    have := op_fix_dual hg.1 (hg.2 a).1
    rwa [op_hpk_e] at this
end PI.RhsWLim.W
