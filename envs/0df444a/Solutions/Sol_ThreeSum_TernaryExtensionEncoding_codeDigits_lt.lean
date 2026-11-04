-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.codeDigits_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:50.933667+00:00
-- url     : https://prove2.me/submissions/0561f10d-d015-455a-8d89-80400724f4f5

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
theorem _root_.solution (code k : ℕ) : codeDigits (p := p) code k<p :=
  Nat.mod_lt _ (Fact.out : p.Prime).pos
end ThreeSum.TernaryExtensionEncoding
