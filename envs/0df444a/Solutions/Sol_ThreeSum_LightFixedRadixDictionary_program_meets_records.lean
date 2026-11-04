-- Prove2me | solution 1 for ThreeSum.LightFixedRadixDictionary.program_meets_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:44.784256+00:00
-- url     : https://prove2.me/submissions/27152be0-e05d-4139-99e1-549a6a353cdf

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_RadixKeyLists_values_eq_map
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedRadixDictionary
open Light RadixKeyLists
variable {lim : Limits}
set_option maxHeartbeats 1400000
namespace ThreeSum.LightFixedRadixDictionary
theorem _root_.solution {R : Type*} (records : List R) (raw : R → ℤ)
    {base dst p U J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base+records.length ≤ dst)
    (hm : 0 < records.length) (hbound : ∀ x ∈ records, |raw x| ≤ (U : ℤ))
    (hspace : LightRadixKeys.space dst records.length J ≤ lim.space)
    (hword : (LightRadixKeys.word p U J : ℤ) ≤ lim.word) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program (records.map raw)) 4 d [base,dst,J,p] μ (time (records.map raw) J)
      (fun r ν => r=((dst+LightRadixKeys.offset records.length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset records.length J)=((records.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset records.length J+1)
          ((tuples records J).map (Radix.positionalHash (p : ℤ) raw)) ∧ Kept μ ν base) := by
  have h := program_meets (records.map raw) μ hw (by simpa using hbase) (by simpa using hm)
    (by intro z hz; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz; exact hbound x hx)
    (by simpa using hspace) hword hd
  simpa only [List.length_map,values_eq_map] using h
end ThreeSum.LightFixedRadixDictionary
