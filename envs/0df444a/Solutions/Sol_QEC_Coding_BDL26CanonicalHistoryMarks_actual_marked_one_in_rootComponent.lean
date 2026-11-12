-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.actual_marked_one_in_rootComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:28:28.509983+00:00
-- url     : https://prove2.me/submissions/38eefff1-328e-4f99-ac63-bdfb60bbc392

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_one
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_oneMarks_in_rootComponent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (j : Nat) (s : Input S (2 * j))
    (u : GraphVertex S 1) (hu : oneNode S (2 * j) u ∈ actualMarks S j s) :
    oneNode S (2 * j) u ∈ actualRootComponent S j s :=
  oneMarks_in_rootComponent S (2 * j) s u ((mem_marks_one S (2 * j) s u).mp hu)
end QEC.Coding.BDL26CanonicalHistoryMarks
