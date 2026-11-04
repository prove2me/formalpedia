-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:05:52.162943+00:00
-- url     : https://prove2.me/submissions/411279f4-8b25-4397-bfc9-339dd068cccf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedGlobalPrefixSetup
theorem _root_.solution {m j F dst bank work d : ℕ} (μ : ℕ→ ℤ)
    (hw : (lim.space:ℤ)≤ lim.word) (hbank : bank+nb m j≤ work)
    (hwork : work+(2*N m j+1)≤ dst) (hspace : dst+8≤ lim.space)
    (hword : (word m j F:ℤ)≤ lim.word) (hd : d+N m j+3≤ lim.depth) :
    Meets lim program 0 d [j,m,F,dst,bank,work] μ (time m j)
      (fun r ν=>r=(dst:ℤ) ∧ Seg ν dst (header m j F bank work) ∧
        Seg ν bank ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν work (2*N m j) ∧ Kept μ ν bank) :=
  meets rfl rfl rfl rfl rfl μ hw hbank hwork hspace hword hd
end ThreeSum.LightWeightedGlobalPrefixSetup
