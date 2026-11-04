-- Prove2me | solution 1 for ThreeSum.LightSignedBoxSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:38:03.721462+00:00
-- url     : https://prove2.me/submissions/675e38fa-aeb8-4bf8-9129-898c520190bb

import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
import Definitions.Def_Submission_ThreeSum_LightSignedBoxSetup
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_meets
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
import Theorems.Thm_ThreeSum_LightSignedLeafTable_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5


set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedBoxSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedBoxSetup
theorem _root_.solution     {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(W+1)*downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap W boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim program 0 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,boxBase,maskBase,work] μ (time W boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (SignedLeaf.value f g stage preL preR) W ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((W+1)*downsetCap W boxCut)) :=
  meets rfl procs rfl rfl rfl rfl rfl rfl rfl rfl rfl preL preR f g
    hw hcut hboxCut hstage hdataL hdataR hbox hmasks hspace hword hvalueWord
    hpreL hpreR hf hg hstoredL hstoredR hd
end ThreeSum.LightSignedBoxSetup
