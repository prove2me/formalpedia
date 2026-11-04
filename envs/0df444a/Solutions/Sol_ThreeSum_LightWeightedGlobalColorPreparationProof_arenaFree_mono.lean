-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparationProof.arenaFree_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:20:18.826475+00:00
-- url     : https://prove2.me/submissions/ed536a42-8b5a-4da0-84c4-346a0fa1727d

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
theorem _root_.solution (free n W J U a b c : ℕ) (ha : a≤n) (hb : b≤n) (hc : c≤n) :
    arenaFree free n W a b c J U≤arenaFree free n W n n n J U :=by
  have hb':=Nat.mul_le_mul_right (J+2) hb
  have hc':=Nat.mul_le_mul_right (J+2) hc
  have ha':=Nat.mul_le_mul_right (2^J) ha
  have ha'':=Nat.mul_le_mul_right (J+2) ha'
  unfold arenaFree work oMatrix positions carry cMatrix bMatrix
  omega
end ThreeSum.LightWeightedGlobalColorPreparationProof
