-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopOwner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:31:40.414662+00:00
-- url     : https://prove2.me/submissions/b380c482-0195-420f-a523-f72d6bb4edd4

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
theorem _root_.solution (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) :
    witnessTopOwner p = Vertex.z p.1 := rfl
end QEC.Coding.BDL26OwnerIncidenceMasks
