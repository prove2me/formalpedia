-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.packed_keys_equal_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:20.881943+00:00
-- url     : https://prove2.me/submissions/3ab79d6b-7d42-4019-9f82-afd6aa13d5e0

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {r : ℕ} (a b : Fin r → ZMod p) :
    coefficientCode a=coefficientCode b ↔ a=b :=
  (coefficientCode_injective r).eq_iff
end ThreeSum.TernaryExtensionEncoding
