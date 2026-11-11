-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.correction_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:02:34.503196+00:00
-- url     : https://prove2.me/submissions/f6c508f5-64e7-424b-a9b9-b02b8a115087

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_relation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXErrorPullback
theorem _root_.solution (h : i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (run S depth i h a).correction =
      (errorSyndrome S depth i a).val +
        ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by
  have hr := BDL26RXDecoderAdapter.rxStepOutput_relation S depth i h (errorSyndrome S depth i a)
  funext z
  exact (CharTwo.eq_add_iff_add_eq.mp (congrFun hr z)).symm
end QEC.Coding.BDL26RXErrorPullback
