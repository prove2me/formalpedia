-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextOwner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:33:32.764186+00:00
-- url     : https://prove2.me/submissions/e931694f-3cf1-493a-a5c3-1f3d198f8a2b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (p : FamilyZ scaleFive 4 (3 : LevelIndex 4)) :
    witnessNextOwner p = rxSyndromeOwner evidenceStateTwo.presentation scaleFive p := by
  rcases p with (⟨x, f⟩ | ⟨q, e⟩) | ⟨z, c⟩ <;> rfl
end QEC.Coding.BDL26OwnerIncidenceMasks
