-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:08:15.65059+00:00
-- url     : https://prove2.me/submissions/6acace22-0d3b-4b15-9128-e4cbeb7bab9f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalReceiptTransport

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalGlobalReceiptTransport
theorem _root_.solution {p : ℕ} [Fact p.Prime] {base d q J c cut : ℕ} {μ ν : ℕ→ℤ}
    (H : LightWeightedGlobalGlobalPreludeProof.Menu μ base d p q J c)
    (K : Kept μ ν cut) (hend : physical base d q J+q*q*(J+2)≤cut) :
    LightWeightedGlobalGlobalPreludeProof.Menu ν base d p q J c := by
  intro s hs i hi
  have hm := Nat.mul_le_mul_right (J+2) (Nat.succ_le_of_lt hs)
  rw [K _ (by nlinarith)]
  exact H s hs i hi
end ThreeSum.WeightedGlobalGlobalReceiptTransport
