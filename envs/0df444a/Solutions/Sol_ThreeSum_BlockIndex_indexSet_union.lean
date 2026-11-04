-- Prove2me | solution 1 for ThreeSum.BlockIndex.indexSet_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:30:45.735333+00:00
-- url     : https://prove2.me/submissions/5408b436-f54c-4bac-b08f-86f97e6bad89

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_Submission_ThreeSum_BlockIndex

set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndex
open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.BlockIndex
theorem _root_.solution {J L : ℕ} (S T : Finset (Coord J L)) :
    indexSet (S∪T) = indexSet S ∪ indexSet T := by
  exact Finset.map_union S T
end ThreeSum.BlockIndex
