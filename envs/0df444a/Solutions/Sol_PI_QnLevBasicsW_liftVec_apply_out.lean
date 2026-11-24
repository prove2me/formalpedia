-- Prove2me | solution 1 for PI.QnLevBasicsW.liftVec_apply_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:35:47.077658+00:00
-- url     : https://prove2.me/submissions/16f064fb-e79c-4588-921a-b59bd637ac96

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
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : liftVec k i r' v p = 0 := by
  simp only [liftVec]
  rw [dif_neg hp]
end PI.QnLevBasicsW
