-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.decode_encoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:39.743342+00:00
-- url     : https://prove2.me/submissions/a403f5c6-9f26-4f58-b580-97b2f9d299a7

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_encode_digit

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    (fun i : Fin f.natDegree => ((encode hf x/p^i.val%p : ℕ) : ZMod p))=
      coefficients hf x := by
  funext i
  rw [encode_digit]
  exact ZMod.natCast_zmod_val _
end ThreeSum.TernaryExtensionEncoding
