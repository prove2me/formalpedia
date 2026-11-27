-- Prove2me | solution 1 for P2M_GlobalTheory_T_dualWeyl_eq_bot_of_not_antitone__5e2731a9d804
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:30.719906+00:00
-- url     : https://prove2.me/submissions/8251d7bb-594f-435f-b5aa-659e26f30e96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualWeylEqBotOfNotAntitone
import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualWeylEqBotOfNotAntitoneStatement
import Theorems.Thm_GlobalTheory_NonDomZero_dualWeyl_eq_bot_of_not_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ), ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  first | exact @GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone | exact GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone | (intros; apply GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone <;> assumption)
end _root_.GlobalTheory.T
