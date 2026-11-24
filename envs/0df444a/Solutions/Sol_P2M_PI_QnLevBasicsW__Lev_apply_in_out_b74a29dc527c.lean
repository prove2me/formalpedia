-- Prove2me | solution 1 for P2M_PI_QnLevBasicsW__Lev_apply_in_out_b74a29dc527c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:32:22.375064+00:00
-- url     : https://prove2.me/submissions/7e13f043-2e1b-48f1-aa5a-d6ce1e5391b9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian

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
theorem _root_.solution (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)
    (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = 0 := by
  simp only [ιLev]
  rw [dif_pos hp, dif_neg hq]
end PI.QnLevBasicsW
