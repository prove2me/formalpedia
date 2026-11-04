-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumerationSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:44.354589+00:00
-- url     : https://prove2.me/submissions/a41d2a11-b712-43dd-8ae1-ff3f1a3cd4d6

import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Definitions.Def_WeightedCache3SUM_Alias_f8e3ce9eb3f48862
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7


set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetEnumerationSetup
theorem _root_.solution {μ : ℕ → ℤ} {L cut dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ work)
    (hd : d+L+2 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,dst,work] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (downsetCap L cut)) :=
  meets rfl rfl rfl rfl hw hspace hword hcut hdst hd
end ThreeSum.LightDownsetEnumerationSetup
