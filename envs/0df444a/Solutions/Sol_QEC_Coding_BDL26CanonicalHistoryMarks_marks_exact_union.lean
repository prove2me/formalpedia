-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.marks_exact_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:27:33.407762+00:00
-- url     : https://prove2.me/submissions/91cf5690-80db-4dd0-9217-ef64e754064a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution : marks S n sigma =
    (Finset.univ.biUnion (fun i : LevelIndex n =>
      (physicalMarks S n sigma i).image (physicalNode S n i))) ∪
    (oneMarks S n sigma).image (oneNode S n) ∪
    (rootMarks S n sigma).image (fun _ => root S n) := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
