-- Prove2me | solution 1 for PI.CharIdemW.charIdem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:02.722853+00:00
-- url     : https://prove2.me/submissions/7eb8cd1a-8446-47ae-ad34-965b42dbc1ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development

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
namespace PI.CharIdemW
theorem _root_.solution (hC : Central) (hS : Scalar) (hM : MulEq) : PI.CharIdem.CharIdem := by
  intro G _ _ V W hV hW
  refine ⟨(hS G V V hV hV).1 ⟨Iso.refl V⟩, (hS G V W hV hW).2, ?_, hC G V, (hM G V W hV hW).2⟩
  exact (hM G V V hV hV).1 ⟨Iso.refl V⟩
end PI.CharIdemW
