-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalExtensionBackendSetup.parameters_with_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:07:13.174569+00:00
-- url     : https://prove2.me/submissions/7c3b9aeb-b5c8-4b33-ac5d-614166812c17

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetupBudget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalExtensionBackendSetup
open LightExtensionBackendLayout TernaryExtensionEncoding WeightedGlobalSignedPadding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000
namespace ThreeSum.LightWeightedGlobalExtensionBackendSetup
theorem _root_.solution (d p q J : ℕ) : d+p+q+J+2 ≤ (p+1)*(q+d+(J+2)+1) := by
  have hh : p ≤ p*(q+d+(J+2)+1) := Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ p+(q+d+(J+2)+1) := by omega
    _ ≤ p*(q+d+(J+2)+1)+(q+d+(J+2)+1) := Nat.add_le_add_right hh _
    _ = _ := by ring
end ThreeSum.LightWeightedGlobalExtensionBackendSetup
