-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:23:20.295371+00:00
-- url     : https://prove2.me/submissions/1c1fa123-808a-4c86-8fd3-db9b0e888c70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_marksWithLower_only_z
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessTopOwner_parent_none
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedComponent_image_eq_singleton


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    componentWithLower lower p hp = {BDL26TopOwnerIsolation.topNode (witnessTopOwner p)} := by
  have hn := witnessTopOwner_parent_none p hp
  unfold componentWithLower
  change parent scaleFive 3 (Vertex.z p.1) = none at hn
  exact BDL26TopOwnerIsolation.markedComponent_image_eq_singleton (marksWithLower lower)
    (marksWithLower_only_z lower) p.1 hn _
end QEC.Coding.BDL26OwnerIncidenceMasks
