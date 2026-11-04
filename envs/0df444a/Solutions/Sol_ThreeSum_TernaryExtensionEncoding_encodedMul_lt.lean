-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.encodedMul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:48.476492+00:00
-- url     : https://prove2.me/submissions/42d60ae2-d35f-4837-b7da-75a78070bf13

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] ThreeSum.TernaryExtensionEncoding._p2m_local_instance_7138b7e7ca_12
variable {f : (ZMod p)[X]}
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (hf : f.Monic) (a b : ℕ) : encodedMul hf a b<p^f.natDegree := by
  unfold encodedMul
  split_ifs
  · exact encode_lt hf _
  · exact pow_pos (Fact.out : p.Prime).pos _
  · exact pow_pos (Fact.out : p.Prime).pos _
end ThreeSum.TernaryExtensionEncoding
