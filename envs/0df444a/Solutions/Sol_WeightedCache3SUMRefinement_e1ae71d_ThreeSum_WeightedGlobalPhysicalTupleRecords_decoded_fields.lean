-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_fields
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:48:06.103234+00:00
-- url     : https://prove2.me/submissions/69c9314c-897b-4936-b651-e52a149a528e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalTupleRecords
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryDecode_dictionary_decode
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords
open WeightedGlobalTupleDictionaryDecode LightTernarySourceHost
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords
