-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.mem_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:42.51969+00:00
-- url     : https://prove2.me/submissions/92bab53a-fa5c-4219-a401-3c2e6be60695

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution {q D r : ℕ} :
    r ∈ digits q D ↔ r ≤ q ∧ q-r ≤ D := by
  simp [digits]
end ThreeSum.TernaryNearEnumeration
