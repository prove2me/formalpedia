-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.words_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:35.855649+00:00
-- url     : https://prove2.me/submissions/28714610-fa1b-48ff-8c75-9da9e6c63656

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_strictly_sorted
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (words qs D).Nodup := by
  have hn : (codes qs D).Nodup := (codes_strictly_sorted qs D hq).imp (fun h => Nat.ne_of_lt h)
  rw [codes_eq_map] at hn
  exact List.Nodup.of_map code hn
end ThreeSum.TernaryNearEnumeration
