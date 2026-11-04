-- Prove2me | solution 1 for ThreeSum.LightMaskUnion.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:46.872865+00:00
-- url     : https://prove2.me/submissions/de40352f-4ed6-4f73-a207-9e483853d143

import Definitions.Def_Submission_ThreeSum_MaskUnion
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c


set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskUnion
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskUnion
theorem _root_.solution {μ : ℕ → ℤ} {W dst work d : ℕ} (A B : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+1 ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,A.card,subsetMask A,subsetMask B,dst,work] μ (time W)
      (fun r μ' => r = (subsetMask (A ∪ B) : ℤ) ∧
        μ' dst = ((A ∪ B).card : ℤ) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst 1) :=
  meets rfl rfl rfl A B hw hdst hspace hword hd
end ThreeSum.LightMaskUnion
