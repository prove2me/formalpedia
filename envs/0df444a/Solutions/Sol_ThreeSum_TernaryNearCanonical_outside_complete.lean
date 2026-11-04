-- Prove2me | solution 1 for ThreeSum.TernaryNearCanonical.outside_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:06.896406+00:00
-- url     : https://prove2.me/submissions/4c2fa805-f965-45cd-a210-67515d83a0d8

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_ThreeSum_TernaryNearCanonical_outside_near_iff

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryNearCanonical
theorem _root_.solution {N T : ℕ} (Q R : TritWord N) (hQ : T<rank Q)
    (hRQ : Below R Q) (hR : T<rank R) :
    ∃ j<(TernaryNearEnumeration.codes (wordList Q) (rank Q-(T+1))).length,
      word Q (rank Q-(T+1)) j=R := by
  exact complete Q R ((outside_near_iff Q R T hQ).mpr ⟨hRQ,hR⟩)
end ThreeSum.TernaryNearCanonical
