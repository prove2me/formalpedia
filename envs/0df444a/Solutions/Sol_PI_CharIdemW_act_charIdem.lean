-- Prove2me | solution 1 for PI.CharIdemW.act_charIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:30.975161+00:00
-- url     : https://prove2.me/submissions/32c6f02e-7866-437e-bdec-c5e1cb94b5fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Theorems.Thm_PI_CharIdemW_act_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (V W : FDRep ℂ G) :
    act W (charIdem V) = ∑ g : G,
      (((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹) • W.ρ g := by
  rw [PI.CharIdem.charIdem, map_sum]
  simp only [act_single]
end PI.CharIdemW
