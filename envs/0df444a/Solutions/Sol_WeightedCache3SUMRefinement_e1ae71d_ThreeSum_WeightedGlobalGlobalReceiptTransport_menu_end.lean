-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:34:28.913977+00:00
-- url     : https://prove2.me/submissions/49feb390-e7a8-48a5-b307-4deb6635165b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalReceiptTransport
import Theorems.Thm_ThreeSum_LightExtensionBackendLayout_end_le


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
theorem _root_.solution (base d p q J : ℕ) :
    physical base d q J+q*q*(J+2)≤base+reserve d p q J := by
  apply le_trans _ (end_le base d p q J)
  unfold sum prod LightExtensionBackendLayout.r h LightExtensionBackendLayout.b a
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
