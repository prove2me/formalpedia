-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPhysicalTupleRecords.decodeRecord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:20:25.484009+00:00
-- url     : https://prove2.me/submissions/cc0f7386-8710-4b1b-ac7e-e5d0f67d53b6

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalTupleRecords
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalTupleRecords
open WeightedGlobalTupleDictionaryDecode LightTernarySourceHost
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*}
namespace ThreeSum.WeightedGlobalPhysicalTupleRecords
theorem _root_.solution (base : List A) (hn : base.Nodup)
    (r M n p : ℕ) (input : ℕ→ℤ) (raw : A→ℤ) :
    Function.Injective (decodeRecord base r M n p input raw) := by
  intro x y he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Fin n×{xs // xs∈RadixKeyLists.tuples base r} => z.1.val) he
  · have hh := congrArg (fun z : Fin n×{xs // xs∈RadixKeyLists.tuples base r} => z.2.val) he
    exact congrArg Fin.val (decode_injective base hn r hh)
end ThreeSum.WeightedGlobalPhysicalTupleRecords
