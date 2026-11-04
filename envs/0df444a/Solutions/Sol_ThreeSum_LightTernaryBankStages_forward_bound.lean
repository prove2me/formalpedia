-- Prove2me | solution 1 for ThreeSum.LightTernaryBankStages.forward_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:48.686198+00:00
-- url     : https://prove2.me/submissions/65b1a3a8-ffc0-4cf9-b8c6-95556e7a1f55

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Theorems.Thm_ThreeSum_TernaryBankStageModel_forwardStage_abs


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryBankStages
theorem _root_.solution {N : ℕ} (k : ℕ) (hk : k≤N)
    (F : TritWord N→ℤ) (V : ℕ) (hF : ∀ R, |F R|≤(V : ℤ)) (R : TritWord N) :
    |forwardStage k F R|≤((4^N*V : ℕ) : ℤ) := by
  have hb := forwardStage_abs k hk F V hF R
  have hp : 4^k≤4^N := Nat.pow_le_pow_right (by omega) hk
  have hm := Nat.mul_le_mul_right V hp
  have hmz : ((4^k : ℕ) : ℤ)*(V : ℤ)≤((4^N*V : ℕ) : ℤ) := by exact_mod_cast hm
  exact hb.trans hmz
end ThreeSum.LightTernaryBankStages
