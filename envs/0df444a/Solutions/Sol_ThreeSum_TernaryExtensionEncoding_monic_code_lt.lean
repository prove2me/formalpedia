-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monic_code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:07.262192+00:00
-- url     : https://prove2.me/submissions/e36dda4e-bac1-4334-ab46-f60a30c0c691

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d code : ℕ} (hc : code<p^d) : code+p^d<p^(d+1) := by
  rw [pow_succ]
  have hp := (Fact.out : p.Prime).one_lt
  have hpos := pow_pos (Fact.out : p.Prime).pos d
  nlinarith
end ThreeSum.TernaryExtensionEncoding
