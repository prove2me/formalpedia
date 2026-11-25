-- Prove2me | solution 1 for PI.GGCardUniWork.cardUni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:39.692414+00:00
-- url     : https://prove2.me/submissions/a2b1b661-5ee4-4680-8c86-81115c0199e9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCardinality_UniMatUpper
import Theorems.Thm_PI_GGCardUniWork_card_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGCardUniWork
open Finset Matrix Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGCardUniWork
theorem _root_.solution : CardUni := by
  intro F _ _ k
  unfold cardU
  rw [Nat.card_congr (uniEquiv (F := F) (k := k)), Nat.card_eq_fintype_card, Fintype.card_fun,
    card_pairs]
end PI.GGCardUniWork
