-- Prove2me | solution 1 for ThreeSum.LightWeightedEnumerationSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:04.307081+00:00
-- url     : https://prove2.me/submissions/06ed3d1e-6ffd-48d0-b682-0c3b3d947688

import Definitions.Def_Submission_Weighted_LightEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumerationSetup
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedEnumerationSetup
theorem _root_.solution {μ : ℕ → ℤ} {N T dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*N+1) ≤ lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((1025*N+1100 : ℕ) : ℤ)≤lim.word)
    (hcut : T ≤ 1025*N) (hdst : dst+(codes N T).length ≤ work)
    (hd : d+N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,T,dst,work] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst ((codes N T).map (fun (a : ℕ) => (a : ℤ))) ∧
        Powers μ' work (2*N) ∧ KeptBut μ μ' work dst (codes N T).length) :=
  meets rfl rfl rfl hw hspace hword hcontrol hcut hdst hd
end ThreeSum.LightWeightedEnumerationSetup
