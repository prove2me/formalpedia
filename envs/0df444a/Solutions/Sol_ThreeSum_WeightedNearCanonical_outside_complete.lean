-- Prove2me | solution 1 for ThreeSum.WeightedNearCanonical.outside_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:24:44.0162+00:00
-- url     : https://prove2.me/submissions/ccd4f85e-f0a4-400e-bfb5-7ff3e844e5cc

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_WeightedNearCanonical_complete
import Theorems.Thm_ThreeSum_WeightedNearCanonical_outside_near_iff

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedNearCanonical
theorem _root_.solution {N T : ℕ} (Q R : TritWord N) (hQ : T<cacheCost Q)
    (hRQ : Below R Q) (hR : T<cacheCost R) :
    ∃ j<(WeightedNearEnumeration.codes (wordList Q) (cacheCost Q-(T+1))).length,
      word Q (cacheCost Q-(T+1)) j=R := by
  exact complete Q R ((outside_near_iff Q R T hQ).mpr ⟨hRQ,hR⟩)
end ThreeSum.WeightedNearCanonical
