-- Prove2me | solution 1 for ThreeSum.LightTernaryParallelDictionaries.program_meets_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:55.987699+00:00
-- url     : https://prove2.me/submissions/eae8338f-d35f-4fad-a40b-2f035c246c9a

import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
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
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
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
open ThreeSum ThreeSum.LightTernaryParallelDictionaries
open Light RadixKeyLists
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
variable {lim : Limits}
namespace ThreeSum.LightTernaryParallelDictionaries
theorem _root_.solution {R : Type*} (records : List R) (raw0 raw1 raw2 : R → ℤ)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+records.length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 records.length J ≤ base1)
    (hbase1 : base1+records.length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 records.length J ≤ base2)
    (hbase2 : base2+records.length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 records.length J ≤ lim.space)
    (hm : 0 < records.length)
    (hb0 : ∀ x ∈ records, |raw0 x| ≤ (U0 : ℤ))
    (hb1 : ∀ x ∈ records, |raw1 x| ≤ (U1 : ℤ))
    (hb2 : ∀ x ∈ records, |raw2 x| ≤ (U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    Meets lim (program (records.map raw0) (records.map raw1) (records.map raw2)) 15 d
      [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2] μ
      (time (records.map raw0) (records.map raw1) (records.map raw2) J)
      (fun r ν => r=((dst2+LightRadixKeys.offset records.length J : ℕ) : ℤ) ∧
        recordOutput ν dst0 records raw0 p0 J ∧ recordOutput ν dst1 records raw1 p1 J ∧
        recordOutput ν dst2 records raw2 p2 J ∧ Kept μ ν base0) := by
  have hb (raw : R → ℤ) (U : ℕ) (h : ∀ x ∈ records, |raw x| ≤ (U : ℤ)) :
      ∀ x ∈ records.map raw, |x| ≤ (U : ℤ) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact h a ha
  have h := program_meets (records.map raw0) (records.map raw1) (records.map raw2) μ hw
    (by simpa using hbase0) (by simpa using hnext0) (by simpa using hbase1)
    (by simpa using hnext1) (by simpa using hbase2) (by simpa using hspace2)
    (by simpa using hm) (by simpa using hm) (by simpa using hm)
    (hb raw0 U0 hb0) (hb raw1 U1 hb1) (hb raw2 U2 hb2) hw0 hw1 hw2 hd
  simpa only [output,recordOutput,List.length_map,values_eq_map] using h
end ThreeSum.LightTernaryParallelDictionaries
