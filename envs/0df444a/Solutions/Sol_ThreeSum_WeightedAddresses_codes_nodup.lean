-- Prove2me | solution 1 for ThreeSum.WeightedAddresses.codes_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:33:19.936203+00:00
-- url     : https://prove2.me/submissions/7cb756f6-2e56-42a1-b280-b527d53bc0d6

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedAddresses
theorem _root_.solution (n t : ℕ) : (codes n t).Nodup :=
  (codes_strictly_sorted n t).imp (fun h => Nat.ne_of_lt h)
end ThreeSum.WeightedAddresses
