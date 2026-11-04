-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:28.971759+00:00
-- url     : https://prove2.me/submissions/65ecec41-c93c-412b-a87f-145fa0a95e86

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleDictionaryDecode
open LightTernarySourceHost
namespace ThreeSum.WeightedGlobalTupleDictionaryDecode
theorem _root_.solution {A : Type*} (base : List A) (hn : base.Nodup) (r : ℕ)
    (j : Fin (base.length^r)) : (equiv base hn r j).val=decode base r j := rfl
end ThreeSum.WeightedGlobalTupleDictionaryDecode
