-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.lifted_zero_coarseSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:00:22.047648+00:00
-- url     : https://prove2.me/submissions/fe0cabb7-6606-4c4c-ad38-a17f3cc2246c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_zero_run_coarse
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_lifted_run_coarse

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
    (coarseSum S depth i h (liftError S depth i a) 0).val =
      (indexedFamily S depth).coboundary1 i.castSucc a := by
  change (run S depth i h (liftError S depth i a)).coarse.val +
    (run S depth i h 0).coarse.val = _
  rw [lifted_run_coarse, zero_run_coarse, add_zero]
end QEC.Coding.BDL26RXErrorPullback
