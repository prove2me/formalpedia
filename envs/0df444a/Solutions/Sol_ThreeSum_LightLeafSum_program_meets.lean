-- Prove2me | solution 1 for ThreeSum.LightLeafSum.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:28.848699+00:00
-- url     : https://prove2.me/submissions/5c4163db-566e-46fd-8c8d-9b14a3ce59ff

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Theorems.Thm_ThreeSum_LightStageLookup_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_LightZetaStages_program_procs


set_option autoImplicit false
open ThreeSum ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightLeafSum
theorem _root_.solution {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (missing : List (Finset (Fin W)))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,missing.length,maskBase,baseL,baseR,work] μ (time W missing.length)
      (fun r μ' => r = (missing.map (term Q preL preR f g stage)).sum ∧ Kept μ μ' work) :=
  meets rfl rfl rfl rfl rfl rfl program_procs rfl Q preL preR missing f g hw hcut hstage
    hdataL hdataR hmasks hspace hword hproductWord haccWord hdisjL hdisjR hcardL hcardR hf hg
    hvalid hstoredL hstoredR hseg hd
end ThreeSum.LightLeafSum
