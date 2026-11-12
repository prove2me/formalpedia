-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.marksWithLower_only_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:13:06.305259+00:00
-- url     : https://prove2.me/submissions/4cddb507-d504-431c-8821-a334489797f7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessTopMarks_only_z


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (lower : Finset StrictLowerNode) :
    BDL26TopOwnerIsolation.TopMarksAreZ (marksWithLower lower) := by
  intro v hv
  exact witnessTopMarks_only_z v ((marksWithLower_top_iff lower v).mp hv)
end QEC.Coding.BDL26OwnerIncidenceMasks
