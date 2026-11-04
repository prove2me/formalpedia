-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumeration.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:12.232173+00:00
-- url     : https://prove2.me/submissions/793579c4-b096-41e2-b025-425e5056c230

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7


set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetEnumeration
theorem _root_.solution {L cut dst powers d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ powers)
    (hpowers : Powers μ powers L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,dst,powers] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧
        SameOutside μ μ' dst (downsetCap L cut)) :=
  meets rfl rfl hw hspace hword hcut hdst hpowers hd
end ThreeSum.LightDownsetEnumeration
