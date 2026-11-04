-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:04.043094+00:00
-- url     : https://prove2.me/submissions/862937d4-ada9-4e6e-8d5f-b3e4394046da

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost
namespace ThreeSum.WeightedGlobalTupleDictionaryDecode
theorem _root_.solution {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    decode base r j∈RadixKeyLists.tuples base r := List.get_mem _ _
end ThreeSum.WeightedGlobalTupleDictionaryDecode
