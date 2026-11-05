-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:34:29.822298+00:00
-- url     : https://prove2.me/submissions/a4be4bf5-cc83-4d13-877f-91fee5d55b6a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalReceiptTransport

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
theorem _root_.solution {p : ℕ} [Fact p.Prime] {base d q J c cut : ℕ} {μ ν : ℕ→ℤ}
    (H : LightWeightedGlobalGlobalPreludeProof.Menu μ base d p q J c)
    (K : Kept μ ν cut) (hend : physical base d q J+q*q*(J+2)≤cut) :
    LightWeightedGlobalGlobalPreludeProof.Menu ν base d p q J c := by
  intro s hs i hi
  have hm := Nat.mul_le_mul_right (J+2) (Nat.succ_le_of_lt hs)
  rw [K _ (by nlinarith)]
  exact H s hs i hi
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
