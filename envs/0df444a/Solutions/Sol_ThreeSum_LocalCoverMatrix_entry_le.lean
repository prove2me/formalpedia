-- Prove2me | solution 1 for ThreeSum.LocalCoverMatrix.entry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:07:20.068629+00:00
-- url     : https://prove2.me/submissions/470aaaf8-df9d-48bb-8b84-722ebab5412a

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}
namespace ThreeSum.LocalCoverMatrix
theorem _root_.solution (w : Weight L (LocalField h)) (k B r : ℕ) : entry w k B r ≤ 1 := by
  unfold entry LightSupportMark.bit
  split <;> omega
end ThreeSum.LocalCoverMatrix
