-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:07.312675+00:00
-- url     : https://prove2.me/submissions/38235150-a2b5-4e78-a7e9-09f5c06442de

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonicalPairs
theorem _root_.solution (original : ℕ) (as bs : List (ℕ × ℕ)) :
    rowCells original (as++bs)=rowCells original as++rowCells original bs := by
  exact List.flatMap_append ..
end ThreeSum.TernaryWantedCanonicalPairs
