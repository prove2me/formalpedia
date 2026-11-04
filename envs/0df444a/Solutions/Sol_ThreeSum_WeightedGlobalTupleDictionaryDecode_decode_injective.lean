-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:00:36.345399+00:00
-- url     : https://prove2.me/submissions/938d590e-8586-4966-b41d-027f4a03f49f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_WeightedCache3SUM_Alias_03e0bdb6c4745899


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost
namespace ThreeSum.WeightedGlobalTupleDictionaryDecode
theorem _root_.solution {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ) :
    Function.Injective (decode base r) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun t : Fin (RadixKeyLists.tuples base r).length => t.val)
    ((RadixKeyLists.tuples_nodup base hn r).injective_get he)
end ThreeSum.WeightedGlobalTupleDictionaryDecode
