-- Prove2me | solution 1 for UpperTheory.Ram.ord_le_totient_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:30.365072+00:00
-- url     : https://prove2.me/submissions/f36d0db4-2046-4d6a-af38-cc6a2b6444b9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeQS
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeTotientQS
import Theorems.Thm_UpperTheory_KR_two_ord_le_QS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Ram
theorem _root_.solution :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), φ.ord ≤ H.QS.totient ∧ 2 * φ.ord ≤ H.QS := by
  intro φ H
  obtain ⟨h1, h2, -⟩ := UpperTheory.KR.two_ord_le_QS H
  exact ⟨h1, h2⟩
end UpperTheory.Ram
