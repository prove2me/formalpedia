-- Prove2me | solution 1 for ThreeSum.LocalCoverMatrix.radix_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:56:09.004094+00:00
-- url     : https://prove2.me/submissions/5838f100-7fb4-4d3e-ab0d-36f47a792422

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}
namespace ThreeSum.LocalCoverMatrix
theorem _root_.solution {p a b : ℕ} (hb : b < p) : (a*p+b)/p=a := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hb]
  omega
end ThreeSum.LocalCoverMatrix
