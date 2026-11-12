-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.actual_root_marked_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:28:14.624267+00:00
-- url     : https://prove2.me/submissions/ab9a6227-52ab-48fb-aabf-49f1adcb54eb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_root_marked_iff_parented_base

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (j : Nat) (s : Input S (2 * j)) :
    root S (2 * j) ∈ actualMarks S j s ↔
      ∃ v ∈ baseMarks S (2 * j) s, ∃ u, parent S 1 v = some u :=
  root_marked_iff_parented_base S (2 * j) s
end QEC.Coding.BDL26CanonicalHistoryMarks
