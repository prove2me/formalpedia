-- Prove2me | solution 1 for ThreeSum.LightSubsetSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:04.097354+00:00
-- url     : https://prove2.me/submissions/f76168af-3555-427c-b4e1-5efa6dd393d5

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs

set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetSetup
theorem _root_.solution {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+3 ≤ lim.depth) :
    Meets lim program 0 d [L,k,m,work] μ (time L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ Table μ' work L ∧
        Powers μ' (work+tableSize L) L ∧ Kept μ μ' work) :=
  meets program_procs hw hspace hword hm hd
end ThreeSum.LightSubsetSetup
