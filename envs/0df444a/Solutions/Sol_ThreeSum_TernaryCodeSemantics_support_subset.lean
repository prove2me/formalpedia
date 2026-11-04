-- Prove2me | solution 1 for ThreeSum.TernaryCodeSemantics.support_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:55:31.10769+00:00
-- url     : https://prove2.me/submissions/1ff9796d-8d48-46d9-860e-28931b88b92d

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_bitPosition_lt

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryCodeSemantics
theorem _root_.solution {N : ℕ} (w : TritWord N) : support w ⊆ range (2*N) := by
  intro a ha
  obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
  exact mem_range.mpr (bitPosition_lt p)
end ThreeSum.TernaryCodeSemantics
