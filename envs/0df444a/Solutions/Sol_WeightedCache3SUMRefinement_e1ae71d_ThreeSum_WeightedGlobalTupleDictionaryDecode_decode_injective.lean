-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:40:20.302772+00:00
-- url     : https://prove2.me/submissions/99ad23f8-9bd9-408d-866b-9d3b279289e5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_WeightedCache3SUM_Alias_03e0bdb6c4745899


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
theorem _root_.solution {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ) :
    Function.Injective (decode base r) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun t : Fin (RadixKeyLists.tuples base r).length => t.val)
    ((RadixKeyLists.tuples_nodup base hn r).injective_get he)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
