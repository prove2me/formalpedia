-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryLookup.triple_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:43:59.594951+00:00
-- url     : https://prove2.me/submissions/da64ccac-60b8-4426-996e-ada5a9619476

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTupleWitness
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryLookup_tuple_lookup

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryLookup
open LightTernarySourceHost
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryLookup
theorem _root_.solution {A : Type*} (base : List A) (r : ℕ) (xs : List A)
    (hx : xs∈RadixKeyLists.tuples base r) (raw word group : A→ℤ) (p R F : ℕ) :
    ∃ j : ℕ, j<base.length^r ∧
      dictionary (base.map raw) p r j=Radix.positionalHash (p : ℤ) raw xs ∧
      dictionary (base.map word) R r j=Radix.positionalHash (R : ℤ) word xs ∧
      dictionary (base.map group) F r j=Radix.positionalHash (F : ℤ) group xs := by
  obtain ⟨j,hj,h⟩ := tuple_lookup base r xs hx
  exact ⟨j,hj,h raw p,h word R,h group F⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryLookup
