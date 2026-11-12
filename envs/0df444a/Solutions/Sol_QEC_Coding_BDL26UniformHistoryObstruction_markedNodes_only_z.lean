-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.markedNodes_only_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:01:52.710556+00:00
-- url     : https://prove2.me/submissions/147a3e64-f982-42a0-92e9-70266ccc04f1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_topMarks_only_z


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j)) :
    BDL26UniformTopOwnerIsolation.TopMarksAreZ S (2 * j + 3) (markedNodes S j lower) := by
  intro v hv
  exact topMarks_only_z S j v ((markedNodes_top_iff S j lower v).mp hv)
end QEC.Coding.BDL26UniformHistoryObstruction
