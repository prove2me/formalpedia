-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.outside_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:50:28.894774+00:00
-- url     : https://prove2.me/submissions/5bbe7ce4-5c73-4719-985c-9db977b57393

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_outside_near_iff

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
theorem _root_.solution {N T : ℕ} (Q R : TritWord N) (hQ : T<cacheCost Q)
    (hRQ : Below R Q) (hR : T<cacheCost R) :
    ∃ j<(WeightedNearEnumeration.codes (wordList Q) (cacheCost Q-(T+1))).length,
      word Q (cacheCost Q-(T+1)) j=R := by
  exact complete Q R ((outside_near_iff Q R T hQ).mpr ⟨hRQ,hR⟩)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
