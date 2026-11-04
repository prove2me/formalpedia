-- Prove2me | solution 1 for ThreeSum.LightTernaryEnumeration.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:09.444197+00:00
-- url     : https://prove2.me/submissions/b96de455-942c-4df1-b823-3f8d28d926a9

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryEnumeration
theorem _root_.solution {W powers N T pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hN : N ≤ W) (hT : T ≤ 2*W) (hprefix : pref+4^N ≤ 4^W)
    (hdst : dst+(codes N T).length ≤ powers) (hpowers : Powers μ powers (2*W))
    (hd : d+N ≤ lim.depth) :
    Meets lim program 0 d [N,T,pref,dst,powers] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst (output N T pref) ∧ SameOutside μ μ' dst (codes N T).length) :=
  meets rfl hw hspace hword N T pref dst μ hN hT hprefix hdst hpowers d hd
end ThreeSum.LightTernaryEnumeration
