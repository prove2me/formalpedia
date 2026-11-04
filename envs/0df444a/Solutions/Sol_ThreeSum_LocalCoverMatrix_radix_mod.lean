-- Prove2me | solution 1 for ThreeSum.LocalCoverMatrix.radix_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:56:10.172177+00:00
-- url     : https://prove2.me/submissions/d30dac75-b1ad-4c51-a24e-4fcb44e51e12

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}
namespace ThreeSum.LocalCoverMatrix
theorem _root_.solution {p a b : ℕ} (hb : b < p) : (a*p+b)%p=b := by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]
end ThreeSum.LocalCoverMatrix
