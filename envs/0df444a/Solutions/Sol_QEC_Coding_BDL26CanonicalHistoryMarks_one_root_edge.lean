-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.one_root_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:01:57.984542+00:00
-- url     : https://prove2.me/submissions/12d16366-9a5e-4607-bb80-738d2be5515e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_root_connected


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (u : GraphVertex S 1) :
    (decodingGraph S (n + 2)).adjacent (oneNode S n u) (root S n) := by
  apply Or.inr
  apply Or.inr
  refine ⟨⟨0, by omega⟩, ?_⟩
  exact root_connected S (n + 2) (by omega) u
end QEC.Coding.BDL26CanonicalHistoryMarks
