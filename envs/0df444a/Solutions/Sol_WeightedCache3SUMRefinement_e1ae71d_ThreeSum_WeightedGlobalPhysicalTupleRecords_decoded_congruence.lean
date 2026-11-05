-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:48:08.144311+00:00
-- url     : https://prove2.me/submissions/d15a93dc-e5e5-4d44-ad7d-f8b928dc6ef8

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
theorem _root_.solution (base : List A) (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    (M : ℤ)∣input x.val.1-Radix.positionalHash (p : ℤ) raw
      (decodeRecord base r M n p input raw x).2.val := by
  have hx := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.2
  rw [dictionary_decode base r ⟨x.val.2,
    ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.1⟩ raw p] at hx
  exact hx
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords
