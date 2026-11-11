-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.lifted_run_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:04:12.814197+00:00
-- url     : https://prove2.me/submissions/734a57f3-151c-4334-9945-229b0ab3c1cd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_lift_errorSyndrome
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_embedded_coarse


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXErrorPullback
theorem _root_.solution (h : i.val % 2 = 0) (a : Lower S depth i) :
    (run S depth i h (liftError S depth i a)).coarse.val =
      (indexedFamily S depth).coboundary1 i.castSucc a := by
  rw [run, lift_errorSyndrome]
  exact embedded_coarse S depth i h _
end QEC.Coding.BDL26RXErrorPullback
