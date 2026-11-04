-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.meets_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:59:57.409864+00:00
-- url     : https://prove2.me/submissions/2ca60a4c-a497-4b06-9931-758c78c79105

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_time_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_word_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_space_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_depth_le_search
import Theorems.Thm_Light_Meets_mono_time
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_9f151fd16c06b1ef
import Definitions.Def_WeightedCache3SUM_Alias_2311045817689c86
import Definitions.Def_WeightedCache3SUM_Alias_d5eaa25d4585cc6b
import Definitions.Def_WeightedCache3SUM_Alias_da105011ac4dcdd4
import Definitions.Def_WeightedCache3SUM_Alias_942628883105a84f
import Definitions.Def_WeightedCache3SUM_Alias_8622643736b2cec4
import Definitions.Def_WeightedCache3SUM_Alias_04fc0611b78e7896
import Definitions.Def_WeightedCache3SUM_Alias_d3fb44062fe6c749
import Theorems.Thm_ThreeSum_LightLocalCoverResources_depth_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_space_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_time_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_word_le_search
import Definitions.Def_WeightedCache3SUM_Alias_a64b3be7ea8b7b19
import Definitions.Def_WeightedCache3SUM_Alias_0a77a2090c5d3d77
import Definitions.Def_WeightedCache3SUM_Alias_e2ad5e59f3af6ab7
import Definitions.Def_WeightedCache3SUM_Alias_ed969675cd1be1e3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_a00dee90c4e0ea45
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_276ab4baf5d9c1f3
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Definitions.Def_WeightedCache3SUM_Alias_de9d37b5900d1a92
import Definitions.Def_WeightedCache3SUM_Alias_a495b72bdff1a7b5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LocalParameterBounds_space_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_time_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_le_search


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution {lim : Limits} {P : Program} {d pMain n free : ℕ}
    {μ : ℕ → ℤ} (S : LightLocalCoverInit.Procs P pMain)
    (hh : 1 ≤ Scales.microHalf (Scales.inputBits n))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+Scales.localSearch 5000000 n ≤ lim.depth)
    (hspace : free+Scales.localSearch 5000000 n ≤ lim.space)
    (hword : (Scales.localSearch 5000000 n : ℤ) ≤ lim.word) :
    let h := Scales.microHalf (Scales.inputBits n)
    let base := LightLocalCoverInit.base free
    Meets lim P pMain d [h,free] μ (Scales.localSearch 5000000 n)
      (fun r ν => r = (LightLocalCoverMetadata.nextFree base h : ℤ) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν free) := by
  have hd' := depth_le_search hh
  exact (S.meets hw (by omega) ((space_le_search hh).trans hspace)
    ((Int.ofNat_le.mpr (word_le_search hh)).trans hword)).mono_time (time_le_search hh)
end ThreeSum.LightLocalCoverInitResources
