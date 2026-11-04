-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.coefficients_mk_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:22:00.325815+00:00
-- url     : https://prove2.me/submissions/7306ebaf-ac08-445a-aac5-1271cb269600

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
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    (a : Fin f.natDegree → ZMod p) :
    coefficients hf (AdjoinRoot.mk f (vectorPolynomial a))=a := by
  funext i
  change (vectorPolynomial a %ₘ f).coeff i.val=a i
  rw [(modByMonic_eq_self_iff hf).mpr (by
    simpa only [degree_eq_natDegree hf.ne_zero] using vectorPolynomial_degree_lt a)]
  exact vectorPolynomial_coeff a i
end ThreeSum.TernaryExtensionEncoding
