-- Prove2me | solution 1 for ThreeSum.LightCanonicalBoxSum.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:19:46.760046+00:00
-- url     : https://prove2.me/submissions/11a9b050-f882-4495-8785-b29b64425171

import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Theorems.Thm_ThreeSum_LightQueryBox_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
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
open ThreeSum ThreeSum.LightCanonicalBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightCanonicalBoxSum
theorem _root_.solution {μ : ℕ → ℤ} {W cut t base maskBase work B d : ℕ}
    (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W)
    (hdata : base+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+Q.card.choose t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((Q.card.choose t*(2^W*B) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hflags : Q.card-t ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim program 0 d [W,cut,Q.card,subsetMask Q,t,base,maskBase,work] μ (time W Q.card t)
      (fun r μ' =>
        r = ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        KeptBut μ μ' work maskBase (Q.card.choose t)) :=
  meets rfl program_procs Q weight hw hcut hdata hmasks hspace hword haccWord ht hflags hweight hstored hd
end ThreeSum.LightCanonicalBoxSum
