-- Prove2me | solution 1 for PI.QnLevBasicsW.mulVec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:21:18.717508+00:00
-- url     : https://prove2.me/submissions/787f81c4-58a8-46bb-a448-e333c9242747

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5
import Theorems.Thm_PI_QnLevBasicsW_blocks_mulVec_lift

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
    (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k i r' g *ᵥ liftVec k i r' v = liftVec k i r' (g *ᵥ v) := by
  rw [ιLev_eq]
  exact blocks_mulVec_lift g 1 v
end PI.QnLevBasicsW
