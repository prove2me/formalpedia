-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.decode_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:42:43.14099+00:00
-- url     : https://prove2.me/submissions/12866f6b-121b-4d9f-ac9b-6df6fbfd2c4b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_mem
import Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
theorem _root_.solution {A : Type*} (base : List A) (r : ℕ) (j : Fin (base.length^r)) :
    (decode base r j).length=r := (RadixKeyLists.mem_tuples _ _ _).mp (decode_mem _ _ _) |>.1
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
