-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_before_colors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:31:22.504923+00:00
-- url     : https://prove2.me/submissions/5b5569f8-1324-4e00-9c70-23e64e8f6517

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalReceiptTransport
import Theorems.Thm_ThreeSum_WeightedGlobalGlobalReceiptTransport_menu_end

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalGlobalReceiptTransport
theorem _root_.solution (M b p K κ n free : ℕ) :
    physical (backend free) (LightWeightedGlobalDimensions.dim M b p K n (n^κ))
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))+
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)))*
        (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)))*
        (LightWeightedGlobalDimensions.J M b n (n^κ)+2)≤scanFree M b p K κ n free :=
  menu_end _ _ _ _ _
end ThreeSum.WeightedGlobalGlobalReceiptTransport
