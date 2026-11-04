-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monicCandidate_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:47.547507+00:00
-- url     : https://prove2.me/submissions/6fa0a0c6-60de-48b7-ba5e-96324aeb6463

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
theorem _root_.solution {d : ℕ} (a : Fin d → ZMod p) :
    (monicCandidate a).natDegree=d := by
  have h := natDegree_add_eq_left_of_degree_lt
    (p := (X^d : (ZMod p)[X])) (q := vectorPolynomial a)
    (by simpa using vectorPolynomial_degree_lt a)
  simpa only [monicCandidate,natDegree_X_pow] using h
end ThreeSum.TernaryExtensionEncoding
