-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.digitCode_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:05.8592+00:00
-- url     : https://prove2.me/submissions/17061ce6-fd1f-4e29-a4c1-84175431bfbc

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution {d : ℕ} (hd : d < 3) : digitCode d ≤ 3 := by
  unfold digitCode
  split <;> omega
end ThreeSum.TernaryAddresses
