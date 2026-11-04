-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monicCandidate_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:58.065779+00:00
-- url     : https://prove2.me/submissions/535c15c4-678a-444c-9d7b-e6705b84bcf9

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_coeff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} (a : Fin d → ZMod p) (i : Fin d) :
    (monicCandidate a).coeff i.val=a i := by
  rw [monicCandidate,coeff_add,coeff_X_pow,if_neg (by omega),zero_add]
  exact vectorPolynomial_coeff a i
end ThreeSum.TernaryExtensionEncoding
