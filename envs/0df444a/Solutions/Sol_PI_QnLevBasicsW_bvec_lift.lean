-- Prove2me | solution 1 for PI.QnLevBasicsW.bvec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:53.981351+00:00
-- url     : https://prove2.me/submissions/5b0e1964-3096-4218-ae38-3b9ae773b1a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_in
import Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_out

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
theorem _root_.solution (a : Fin (2 * r' + k + 1)) (q : Fin (2 * (i + r') + k + 1)) (hq : q.val = a.val + i) :
    liftVec k i r' (bvec a) = bvec q := by
  funext p
  have ha := a.isLt
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · rw [liftVec_apply_in (bvec a) p ⟨p.val - i, by omega⟩ (by simp only [Fin.val_mk]; omega)]
    simp only [bvec, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [liftVec_apply_out _ p hp]
    simp only [bvec, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
end PI.QnLevBasicsW
