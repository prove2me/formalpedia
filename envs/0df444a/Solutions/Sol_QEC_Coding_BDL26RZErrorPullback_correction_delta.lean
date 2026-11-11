-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.correction_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:31:28.160397+00:00
-- url     : https://prove2.me/submissions/1a772c25-0f2c-4edd-b2a3-0ec4e3cf4dfe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_relation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RZErrorPullback
theorem _root_.solution (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (run S depth i h a).correction =
      (errorSyndrome S depth i a).val +
        ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by
  have hr := BDL26RZDecoderAdapter.rzStepOutput_relation S depth i h (errorSyndrome S depth i a)
  funext z
  exact (CharTwo.eq_add_iff_add_eq.mp (congrFun hr z)).symm
end QEC.Coding.BDL26RZErrorPullback
