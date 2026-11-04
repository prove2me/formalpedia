-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.decode_field_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:22.0221+00:00
-- url     : https://prove2.me/submissions/2527eb74-6c6b-492c-903e-d1866e15e2aa

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_decode_encoded


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic) (code : Fin (p^f.natDegree)) :
    coefficients hf ((encodedEquiv hf).symm code)=coefficientVector f.natDegree code.val := by
  have he : encode hf ((encodedEquiv hf).symm code)=code.val :=
    congrArg Fin.val ((encodedEquiv hf).apply_symm_apply code)
  have h := decode_encoded hf ((encodedEquiv hf).symm code)
  rw [he] at h
  exact h.symm
end ThreeSum.TernaryExtensionEncoding
