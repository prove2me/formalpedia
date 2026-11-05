-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_before_colors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:39.674036+00:00
-- url     : https://prove2.me/submissions/cf431049-28f0-4a8a-a0f5-8e9b2c6afacf

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalReceiptTransport
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGlobalReceiptTransport_menu_end

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
theorem _root_.solution (M b p K κ n free : ℕ) :
    physical (backend free) (LightWeightedGlobalDimensions.dim M b p K n (n^κ))
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))+
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)))*
        (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)))*
        (LightWeightedGlobalDimensions.J M b n (n^κ)+2)≤scanFree M b p K κ n free :=
  menu_end _ _ _ _ _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
