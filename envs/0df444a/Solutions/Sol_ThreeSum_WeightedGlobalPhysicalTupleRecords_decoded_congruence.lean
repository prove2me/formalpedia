-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPhysicalTupleRecords.decoded_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:21:19.354006+00:00
-- url     : https://prove2.me/submissions/a537337e-519b-4f92-98b4-2fc98be32049

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
theorem _root_.solution (base : List A) (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ)
    (x : TernarySourceHostModel.records M n (base.length^r) input
      (dictionary (base.map raw) p r)) :
    (M : ℤ)∣input x.val.1-Radix.positionalHash (p : ℤ) raw
      (decodeRecord base r M n p input raw x).2.val := by
  have hx := ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.2
  rw [dictionary_decode base r ⟨x.val.2,
    ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp x.property).2.1⟩ raw p] at hx
  exact hx
end ThreeSum.WeightedGlobalPhysicalTupleRecords
