-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:02:11.338056+00:00
-- url     : https://prove2.me/submissions/d51f96e6-8b86-4d98-a65a-feecac0a6203

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_mem
import Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost
namespace ThreeSum.WeightedGlobalTupleDictionaryDecode
theorem _root_.solution {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    (decode base r j).length=r := (RadixKeyLists.mem_tuples _ _ _).mp (decode_mem _ _ _) |>.1
end ThreeSum.WeightedGlobalTupleDictionaryDecode
