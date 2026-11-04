-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_fields
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:40:13.921898+00:00
-- url     : https://prove2.me/submissions/f46be81c-4abc-470b-80bf-40ea082d8df3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalTupleRecords
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_dictionary_decode
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalTupleRecords
open WeightedGlobalTupleDictionaryDecode LightTernarySourceHost
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*}
namespace ThreeSum.WeightedGlobalPhysicalTupleRecords
theorem _root_.solution (base : List A) (r M n p R F : ℕ) (input : ℕ→ℤ)
    (raw word group : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    dictionary (base.map word) R r x.val.2=
      Radix.positionalHash (R : ℤ) word (decodeRecord base r M n p input raw x).2.val ∧
    dictionary (base.map group) F r x.val.2=
      Radix.positionalHash (F : ℤ) group (decodeRecord base r M n p input raw x).2.val := by
  let j : Fin (base.length^r) := ⟨x.val.2,
    ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.1⟩
  exact ⟨dictionary_decode base r j word R,dictionary_decode base r j group F⟩
end ThreeSum.WeightedGlobalPhysicalTupleRecords
