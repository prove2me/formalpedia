-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monicCandidate_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:33.861229+00:00
-- url     : https://prove2.me/submissions/49b4cf50-7ef0-4755-bc80-6998ec52acc3

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_coeff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (d : ℕ) :
    Function.Injective (monicCandidate (p := p) (d := d)) := by
  intro a b h
  funext i
  have hc := congrArg (fun f : (ZMod p)[X] => f.coeff i.val) h
  simpa only [monicCandidate_coeff] using hc
end ThreeSum.TernaryExtensionEncoding
