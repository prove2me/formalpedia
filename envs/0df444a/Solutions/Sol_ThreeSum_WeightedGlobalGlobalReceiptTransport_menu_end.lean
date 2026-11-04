-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:08:02.446207+00:00
-- url     : https://prove2.me/submissions/cd0d005a-293b-490c-bbb5-f7caba764144

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalReceiptTransport
import Theorems.Thm_ThreeSum_LightExtensionBackendLayout_end_le


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalGlobalReceiptTransport
theorem _root_.solution (base d p q J : ℕ) :
    physical base d q J+q*q*(J+2)≤base+reserve d p q J := by
  apply le_trans _ (end_le base d p q J)
  unfold sum prod LightExtensionBackendLayout.r h LightExtensionBackendLayout.b a
  omega
end ThreeSum.WeightedGlobalGlobalReceiptTransport
