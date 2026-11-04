-- Prove2me | solution 1 for ThreeSum.LightZetaPass.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:56.995354+00:00
-- url     : https://prove2.me/submissions/3f366c5a-bd55-4f5b-ae02-39b2c7c26086

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs


set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaPass
theorem _root_.solution {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ}
    (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hsrc : src+downsetCap L cut ≤ maskBase) (hdst : dst+downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hsep : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,a.val,src,dst,maskBase,work] μ (time L cut)
      (fun _ μ' => TableAt μ' dst cut (Subset.zetaStep a f) ∧
        KeptBut μ μ' maskBase dst (downsetCap L cut)) :=
  meets rfl rfl rfl rfl rfl program_procs rfl rfl a f hw hcut hsrc hdst hmasks hsep
    hspace hword hvalueWord hread hvalues hd
end ThreeSum.LightZetaPass
