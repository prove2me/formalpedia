-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.decode_monic_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:57.824207+00:00
-- url     : https://prove2.me/submissions/aab227ab-d8b6-4f99-8dc5-52d7a857f167

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicVector_code
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_code_coefficientVector


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d code : ℕ} (hc : code<p^d) :
    coefficientVector (p := p) (d+1) (code+p^d)=monicVector (coefficientVector d code) := by
  have he : coefficientCode (monicVector (coefficientVector (p := p) d code))=code+p^d := by
    rw [monicVector_code,code_coefficientVector hc]
  rw [← he,coefficientVector_code]
end ThreeSum.TernaryExtensionEncoding
