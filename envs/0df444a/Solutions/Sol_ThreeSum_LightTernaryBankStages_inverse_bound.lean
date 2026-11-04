-- Prove2me | solution 1 for ThreeSum.LightTernaryBankStages.inverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:37:20.473208+00:00
-- url     : https://prove2.me/submissions/e5586d48-b178-4ef9-81c9-06e5901c937f

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_abs


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryBankStages
theorem _root_.solution {N : ℕ} (k : ℕ) (hk : k≤N)
    (H : TritWord N→ℤ) (V : ℕ) (hH : ∀ R, |H R|≤(V : ℤ)) (R : TritWord N) :
    |stageValue k H R|≤((4^N*V : ℕ) : ℤ) := by
  have hb := stageValue_abs k hk H V hH R
  have hp : 4^k≤4^N := Nat.pow_le_pow_right (by omega) hk
  have hm := Nat.mul_le_mul_right V hp
  have hmz : ((4^k : ℕ) : ℤ)*(V : ℤ)≤((4^N*V : ℕ) : ℤ) := by exact_mod_cast hm
  exact hb.trans hmz
end ThreeSum.LightTernaryBankStages
