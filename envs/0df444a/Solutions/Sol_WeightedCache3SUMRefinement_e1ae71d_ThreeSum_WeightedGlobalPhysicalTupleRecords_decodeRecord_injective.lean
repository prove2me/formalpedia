-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords.decodeRecord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:48:49.112203+00:00
-- url     : https://prove2.me/submissions/ef1d0449-21c9-43bc-a5e2-e98b63bffa61

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalTupleRecords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_injective


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
theorem _root_.solution (base : List A) (hn : base.Nodup)
    (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ) :
    Function.Injective (decodeRecord base r M n p input raw) := by
  intro x y he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Fin n×{xs // xs∈RadixKeyLists.tuples base r} => z.1.val) he
  · have hh := congrArg (fun z : Fin n×{xs // xs∈RadixKeyLists.tuples base r} => z.2.val) he
    exact congrArg Fin.val (decode_injective base hn r hh)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalTupleRecords
