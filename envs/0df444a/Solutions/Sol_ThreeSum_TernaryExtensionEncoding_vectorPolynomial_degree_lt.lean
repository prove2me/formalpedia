-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.vectorPolynomial_degree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:51.123724+00:00
-- url     : https://prove2.me/submissions/99f80696-4712-476a-895c-5d30463c1457

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} (a : Fin d → ZMod p) :
    (vectorPolynomial a).degree < d := by
  unfold vectorPolynomial
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt a
end ThreeSum.TernaryExtensionEncoding
