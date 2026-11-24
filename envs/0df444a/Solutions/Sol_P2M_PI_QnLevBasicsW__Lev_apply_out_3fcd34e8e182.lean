-- Prove2me | solution 1 for P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:32:24.08216+00:00
-- url     : https://prove2.me/submissions/d8382214-9ad8-49af-91e6-bc9cd1be3c14

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
    (p q : Fin (2 * (i + r') + k + 1)) (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]
end PI.QnLevBasicsW
