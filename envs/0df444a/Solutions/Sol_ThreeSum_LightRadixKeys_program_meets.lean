-- Prove2me | solution 1 for ThreeSum.LightRadixKeys.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:42:09.894198+00:00
-- url     : https://prove2.me/submissions/308eb1f6-da0b-49e6-a737-5dd22efec26e

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightRadixKeys
theorem _root_.solution {src dst p U J d : ℕ} {μ : ℕ → ℤ}
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hspace : space dst base.length J ≤ lim.space) (hword : (word p U J : ℤ) ≤ lim.word)
    (hd : d+J+2 ≤ lim.depth) (hread : Seg μ src base) :
    Meets lim program 0 d [src,base.length,J,p,dst] μ (time base.length J)
      (fun r ν => r = ((dst+offset base.length J : ℕ) : ℤ) ∧
        ν (dst+offset base.length J) = ((base.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+offset base.length J+1) (values (p : ℤ) base J) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl base hw hsrc hm hbound J d μ hspace hword hd hread
end ThreeSum.LightRadixKeys
