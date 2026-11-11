-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.correction_difference_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:57:38.528694+00:00
-- url     : https://prove2.me/submissions/8803f222-288e-4f0b-a3dd-0958857bfb9b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_correction_delta

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXErrorPullback
theorem _root_.solution (h : i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((run S depth i h a).correction + (run S depth i h b).correction) =
    (errorSyndrome S depth i a).val + (errorSyndrome S depth i b).val +
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by
  rw [map_add, correction_delta S depth i h a, correction_delta S depth i h b]
  change _ = _ + _ + ((indexedDecoderData S depth).selectedMap i).map2
    ((run S depth i h a).coarse.val + (run S depth i h b).coarse.val)
  rw [map_add]
  abel
end QEC.Coding.BDL26RXErrorPullback
