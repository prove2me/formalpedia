-- Prove2me | solution 1 for ThreeSum.LightZetaCell.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:41.378595+00:00
-- url     : https://prove2.me/submissions/8636c836-9fe7-48cf-b114-00835acff574

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs


set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaCell
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaCell
theorem _root_.solution {μ : ℕ → ℤ} {L cut src dst work U d : ℕ}
    (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,S.card,subsetMask S,a.val,src,dst,work] μ (time L)
      (fun _ μ' => μ' (dst+subsetRank S) = Subset.zetaStep a f S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) :=
  meets rfl program_procs rfl rfl S a f hw hsrc hdst hspace hword hvalueWord hread hvalues hS hd
end ThreeSum.LightZetaCell
