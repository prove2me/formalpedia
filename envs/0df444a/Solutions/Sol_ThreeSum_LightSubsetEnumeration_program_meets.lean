-- Prove2me | solution 1 for ThreeSum.LightSubsetEnumeration.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:04.834446+00:00
-- url     : https://prove2.me/submissions/d8c36f87-3d5a-472b-8457-f66eb1db7ab1

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetEnumeration
theorem _root_.solution {W powers L k pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hk : k ≤ W+1) (hprefix : pref+2^L ≤ 2^W)
    (hdst : dst+L.choose k ≤ powers) (hpowers : Powers μ powers W)
    (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,k,pref,dst,powers] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        Seg μ' dst (output L k pref) ∧ SameOutside μ μ' dst (L.choose k)) :=
  meets rfl hw hspace hword L k pref dst μ hL hk hprefix hdst hpowers d hd
end ThreeSum.LightSubsetEnumeration
