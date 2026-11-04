-- Prove2me | solution 1 for ThreeSum.LightSparseQuery.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:32:24.587803+00:00
-- url     : https://prove2.me/submissions/f7111c79-d66c-4a38-85f8-af09beb9a471

import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Definitions.Def_Submission_ThreeSum_LightSparseQuery
import Theorems.Thm_ThreeSum_LightSparseQuery_meets
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
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
open ThreeSum ThreeSum.LightSparseQuery
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open scoped BigOperators
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSparseQuery
theorem _root_.solution    {μ : ℕ → ℤ} {W cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(W+1)*downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+queryItems Q.card t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (magnitudeBound W stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (SignedLeaf.value f g stage preL preR) W)
    (hd : d+W+9 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,baseL,baseR,boxCut,boxBase,maskBase,work] μ (time W Q.card t)
      (fun r μ' =>
        r = Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
          SubsetStages.stageValue g stage (preR ∪ S)) Q ∧
        KeptBut μ μ' work maskBase (queryItems Q.card t)) :=
  meets rfl rfl rfl rfl explicitProcs boxProcs Q preL preR f g hw hcut hstage
    hdataL hdataR hdataBox hmasks hspace hword hvalueWord ht hboxCut hflags hdisjL hdisjR
    hcardL hcardR hf hg hstoredL hstoredR hstoredBox hd
end ThreeSum.LightSparseQuery
