-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.arrayPolynomial_as_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:24:10.751617+00:00
-- url     : https://prove2.me/submissions/14172c9f-7fff-46fc-b16c-79fb5f921808

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (n : ℕ) (a : ℕ → ℕ) :
    arrayPolynomial (p := p) n a=vectorPolynomial (fun i : Fin n => (a i.val : ZMod p)) := by
  unfold arrayPolynomial vectorPolynomial
  rw [← Fin.sum_univ_eq_sum_range]
end ThreeSum.TernaryExtensionEncoding
