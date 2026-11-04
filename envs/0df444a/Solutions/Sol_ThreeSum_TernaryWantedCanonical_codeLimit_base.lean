-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonical.codeLimit_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:19.186607+00:00
-- url     : https://prove2.me/submissions/ea04f4ef-83a7-4980-bf5a-f61bcbafcb88

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonical
theorem _root_.solution {N code R j : ℕ} (hN : 1 ≤ N) :
    code+R ≤ codeLimit N code R j := by
  unfold codeLimit
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
end ThreeSum.TernaryWantedCanonical
