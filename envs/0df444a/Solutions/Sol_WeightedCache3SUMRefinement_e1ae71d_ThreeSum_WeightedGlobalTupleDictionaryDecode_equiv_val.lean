-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:38:12.4552+00:00
-- url     : https://prove2.me/submissions/401150bc-397b-4e37-bd74-291e621451f7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
theorem _root_.solution {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ)
    (j : Fin (base.length^r)) : (equiv base hn r j).val=decode base r j := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTupleDictionaryDecode
