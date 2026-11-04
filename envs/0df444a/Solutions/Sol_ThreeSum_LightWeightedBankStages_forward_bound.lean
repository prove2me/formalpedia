-- Prove2me | solution 1 for ThreeSum.LightWeightedBankStages.forward_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:33:19.579615+00:00
-- url     : https://prove2.me/submissions/4f5291c5-4fee-4004-919b-732c47437821

import Definitions.Def_Submission_Weighted_BankSweep
import Definitions.Def_Submission_Weighted_BankStages
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_abs


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedBankStages
theorem _root_.solution {N : ℕ} (k : ℕ) (hk : k≤N)
    (F : TritWord N→ℤ) (V : ℕ) (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage k F R|≤((4^N*V : ℕ) : ℤ) := by
  have hb := forwardStage_abs k hk F V hF R
  have hp : 4^k≤4^N := Nat.pow_le_pow_right (by omega) hk
  have hm := Nat.mul_le_mul_right V hp
  have hmz : ((4^k : ℕ) : ℤ)*(V : ℤ)≤((4^N*V : ℕ) : ℤ) := by exact_mod_cast hm
  exact hb.trans hmz
end ThreeSum.LightWeightedBankStages
