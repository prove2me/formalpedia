-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparationProof.buildTime_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:18:36.953223+00:00
-- url     : https://prove2.me/submissions/1050ac55-9f1d-4ce2-b771-820d4372bd72

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalColorPreparationProof
theorem _root_.solution (n J U a b c : ℕ) (ha : a≤n) (hb : b≤n) (hc : c≤n) :
    buildTime a b c J U≤buildTime n n n J U :=by
  have hb':=Nat.mul_le_mul_right (LightTernarySignedRow.time J (3*U)+200) hb
  have hc':=Nat.mul_le_mul_right (LightTernarySignedRow.time J (3*U)+200) hc
  have ha':=Nat.mul_le_mul_right (LightTernaryRequesterMatrix.innerTime (2^J) J U+200) ha
  unfold buildTime LightTernarySignedMatrix.time LightTernaryRequesterMatrix.time
  omega
end ThreeSum.LightWeightedGlobalColorPreparationProof
