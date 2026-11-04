-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monicCandidate_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:53.053988+00:00
-- url     : https://prove2.me/submissions/8b83d4a2-10bc-4b0b-9a68-48aab9b94131

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_degree_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} (a : Fin d → ZMod p) : (monicCandidate a).Monic := by
  exact monic_X_pow_add (vectorPolynomial_degree_lt a)
end ThreeSum.TernaryExtensionEncoding
