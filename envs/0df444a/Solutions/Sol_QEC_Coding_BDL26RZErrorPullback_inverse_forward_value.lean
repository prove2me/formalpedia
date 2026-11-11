-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.inverse_forward_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:26:01.078812+00:00
-- url     : https://prove2.me/submissions/cd1fd70d-9f2b-4b3d-a458-c5be046f0d34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RZErrorPullback
theorem _root_.solution (v : Cocycle (state S i.val).presentation) :
    (nextCocycle S i.val (state S i.val) v).val =
      ((indexedDecoderData S depth).selectedMap i).map1 v.val := by
  rw [selectedMap_eq]
  rfl
end QEC.Coding.BDL26RZErrorPullback
