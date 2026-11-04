-- Prove2me | solution 1 for ThreeSum.LightQueryBox.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:02:27.900665+00:00
-- url     : https://prove2.me/submissions/82dbc8ba-b66c-48ec-928a-e674e43e288b

import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Theorems.Thm_ThreeSum_LightQueryBox_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Theorems.Thm_ThreeSum_LightBoxStages_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Theorems.Thm_ThreeSum_LightStageLookup_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Theorems.Thm_ThreeSum_LightZetaPass_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_LightZetaStages_program_procs


set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryBox
open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryBox
theorem _root_.solution {μ : ℕ → ℤ} {L cut base work d : ℕ}
    (Q U : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hU : U ⊆ Q) (hflags : (Q \ U).card ≤ cut)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,Q.card,subsetMask Q,U.card,subsetMask U,base,work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        Kept μ μ' work) :=
  meets rfl rfl rfl rfl rfl program_procs rfl rfl Q U weight hw hcut hdata hspace hword
    hU hflags hstored hd
end ThreeSum.LightQueryBox
