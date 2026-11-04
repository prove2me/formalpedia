-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTupleDictionaryLookup.triple_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:42.368807+00:00
-- url     : https://prove2.me/submissions/e4c997b9-bb7c-4f97-9076-f91e0bde9661

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTupleWitness
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryLookup_tuple_lookup

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryLookup
open LightTernarySourceHost
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalTupleDictionaryLookup
theorem _root_.solution {A : Type*} (base : List A) (r : ℕ) (xs : List A)
    (hx : xs∈RadixKeyLists.tuples base r) (raw word group : A→ℤ) (p R F : ℕ) :
    ∃ j : ℕ, j<base.length^r ∧
      dictionary (base.map raw) p r j=Radix.positionalHash (p : ℤ) raw xs ∧
      dictionary (base.map word) R r j=Radix.positionalHash (R : ℤ) word xs ∧
      dictionary (base.map group) F r j=Radix.positionalHash (F : ℤ) group xs := by
  obtain ⟨j,hj,h⟩ := tuple_lookup base r xs hx
  exact ⟨j,hj,h raw p,h word R,h group F⟩
end ThreeSum.WeightedGlobalTupleDictionaryLookup
