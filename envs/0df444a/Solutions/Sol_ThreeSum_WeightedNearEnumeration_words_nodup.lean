-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.words_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:32.851771+00:00
-- url     : https://prove2.me/submissions/f819b3f5-0d11-4601-bbc3-770f787fb12a

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_strictly_sorted
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_strictly_sorted


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (words qs D).Nodup := by
  have hn : (codes qs D).Nodup := (codes_strictly_sorted qs D hq).imp (fun h => Nat.ne_of_lt h)
  rw [codes_eq_map] at hn
  exact List.Nodup.of_map code hn
end ThreeSum.WeightedNearEnumeration
