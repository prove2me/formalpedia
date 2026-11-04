-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.codes_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:53.383613+00:00
-- url     : https://prove2.me/submissions/6e017e95-bf1b-4abe-9b89-562a961e7a0b

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution (n t : ℕ) : (codes n t).Nodup :=
  (codes_strictly_sorted n t).imp (fun h => Nat.ne_of_lt h)
end ThreeSum.TernaryAddresses
