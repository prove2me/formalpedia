-- Prove2me | solution 1 for PI.OneCosetSharp.W.oneCosetSharp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:28.714125+00:00
-- url     : https://prove2.me/submissions/6f22be44-96a4-4699-b25a-9e9b8577d71d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_OneCosetSharpOfPatClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.OneCosetSharp PI.OneCosetSharp.W
namespace PI.OneCosetSharp.W
theorem _root_.solution (h1 : Claim1) (h2 : Claim2) : OneCosetSharp := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hk hm hm4 hj1 hj2 hc ha hb
  exact ⟨h1 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩ ,
    h2 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩⟩
end PI.OneCosetSharp.W
