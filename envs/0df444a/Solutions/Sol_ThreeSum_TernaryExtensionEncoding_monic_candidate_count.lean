-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monic_candidate_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:14.72492+00:00
-- url     : https://prove2.me/submissions/76ef36c8-c796-4bb3-935b-dad2cc0a09e4

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_injective

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (d : ℕ) :
    (univ.image (monicCandidate (p := p) (d := d))).card=p^d := by
  rw [card_image_of_injective _ (monicCandidate_injective d)]
  simp
end ThreeSum.TernaryExtensionEncoding
