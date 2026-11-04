-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.mk_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:15.996704+00:00
-- url     : https://prove2.me/submissions/eb0b8112-e935-464a-b0e1-2feeb1a03b61

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_decode_encoded
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_coefficients_mk_vector


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    AdjoinRoot.mk f (vectorPolynomial
      (fun i : Fin f.natDegree => ((encode hf x/p^i.val%p : ℕ) : ZMod p)))=x := by
  rw [decode_encoded]
  apply (coefficients hf).injective
  exact coefficients_mk_vector hf _
end ThreeSum.TernaryExtensionEncoding
