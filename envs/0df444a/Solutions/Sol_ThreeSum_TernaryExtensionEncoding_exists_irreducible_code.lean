-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.exists_irreducible_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:56.746801+00:00
-- url     : https://prove2.me/submissions/b1a0c450-83eb-430b-b81b-de0dd1a7e217

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_exists_irreducible_candidate


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (d : ℕ) (hd : 0<d) :
    ∃ code<p^d, Irreducible (monicOfCode (p := p) d code) := by
  obtain ⟨a,ha⟩ := exists_irreducible_candidate (p := p) d hd
  refine ⟨coefficientCode a,coefficientCode_lt a,?_⟩
  simpa only [monicOfCode,coefficientVector_code] using ha
end ThreeSum.TernaryExtensionEncoding
