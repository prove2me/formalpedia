-- Prove2me | solution 1 for P2M_Formalism_Q3_mul_ne_one_iff__67a0a7119a81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:23.65979+00:00
-- url     : https://prove2.me/submissions/ae5bb5d6-098c-42c7-ad89-19903157f281

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA
import Theorems.Thm_Formalism_Q3_cc_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.Q3
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}
namespace Formalism.Q3
theorem _root_.solution (hc : c * c = 1) (g : G) : c * g ≠ 1 ↔ g ≠ c := by
  constructor
  · rintro h rfl
    exact h hc
  · intro h h'
    apply h
    have := cc_mul hc g
    rw [h', mul_one] at this
    exact this.symm
end Formalism.Q3
