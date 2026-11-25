-- Prove2me | solution 1 for PI.QnLevBasicsW.level_group_isotropic_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:52.010984+00:00
-- url     : https://prove2.me/submissions/db454623-56df-45d6-b92c-da9521a833f6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_in
import Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_out
import Theorems.Thm_PI_QnLevBasicsW_herm_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution : LevWb := by
  intro k i r' z hz
  refine ⟨?_, ?_⟩
  · unfold inWb at hz ⊢
    intro p hp
    by_cases hb : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · have ha : p.val - i < 2 * r' + k + 1 := by omega
      rw [liftVec_apply_in z p ⟨p.val - i, ha⟩ (by simp only [Fin.val_mk]; omega)]
      exact hz _ (by simp only [Fin.val_mk]; omega)
    · exact liftVec_apply_out z p hb
  · unfold Tz
    rw [herm_lift]
end PI.QnLevBasicsW
