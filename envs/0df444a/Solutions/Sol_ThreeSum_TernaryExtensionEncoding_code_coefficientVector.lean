-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.code_coefficientVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:04.973183+00:00
-- url     : https://prove2.me/submissions/b0601424-c2cf-406a-8b1d-7abf0de79eda

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d code : ℕ} (hc : code<p^d) :
    coefficientCode (coefficientVector (p := p) d code)=code := by
  obtain ⟨a,ha⟩ := (coefficientEquiv (p := p) d).surjective ⟨code,hc⟩
  have he : coefficientCode a=code := congrArg Fin.val ha
  rw [← he,coefficientVector_code]
end ThreeSum.TernaryExtensionEncoding
