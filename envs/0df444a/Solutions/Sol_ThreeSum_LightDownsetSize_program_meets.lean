-- Prove2me | solution 1 for ThreeSum.LightDownsetSize.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:06.021192+00:00
-- url     : https://prove2.me/submissions/54aec47f-18ed-474e-8051-545175149cee

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs


set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetSize
theorem _root_.solution {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,work] μ (time L)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧ Kept μ μ' work) :=
  meets rfl program_procs rfl hw hspace hword hcut hd
end ThreeSum.LightDownsetSize
