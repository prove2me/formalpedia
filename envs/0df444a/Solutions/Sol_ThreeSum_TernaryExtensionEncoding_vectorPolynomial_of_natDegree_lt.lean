-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.vectorPolynomial_of_natDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:18.63258+00:00
-- url     : https://prove2.me/submissions/c1d38ce8-6bf2-41a7-99f0-90b66c8711d5

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_coeff
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_degree_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.natDegree<d) : vectorPolynomial (fun i : Fin d => f.coeff i.val)=f := by
  ext k
  by_cases hk : k<d
  · exact vectorPolynomial_coeff _ ⟨k,hk⟩
  · have hg : (vectorPolynomial (fun i : Fin d => f.coeff i.val)).coeff k=0 := by
      apply coeff_eq_zero_of_degree_lt
      exact (vectorPolynomial_degree_lt _).trans_le (by exact_mod_cast Nat.le_of_not_lt hk)
    rw [hg,coeff_eq_zero_of_natDegree_lt (by omega)]
end ThreeSum.TernaryExtensionEncoding
