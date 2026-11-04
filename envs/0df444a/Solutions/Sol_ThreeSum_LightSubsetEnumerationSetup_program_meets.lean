-- Prove2me | solution 1 for ThreeSum.LightSubsetEnumerationSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:59.66246+00:00
-- url     : https://prove2.me/submissions/adb73646-7021-45f0-9e16-d04264250fb3

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7


set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetEnumerationSetup
theorem _root_.solution {μ : ℕ → ℤ} {L k dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hk : k ≤ L+1) (hdst : dst+L.choose k ≤ work)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,k,dst,work] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        SegN μ' dst (enumerateLayer L k) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (L.choose k)) :=
  meets rfl rfl rfl hw hspace hword hk hdst hd
end ThreeSum.LightSubsetEnumerationSetup
